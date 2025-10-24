#include <optional>
#include <vector>
#include <span>
#include <cstdint>
#include <cassert>
#include <algorithm>
#include <cstring>

#include "Parameters.hpp"
#include <unordered_map>
#include <unordered_set>
#include <cmath>

const uint64_t rand_num = 0x9e3779b97f4a7c15ULL;

struct RangeIndex {
    uint32_t Min, Max;
};

struct BloomParams { size_t m_bits; size_t k_hashes; size_t byte_size() const { return (m_bits + 7) / 8; }};

static inline BloomParams bloom_params_for(size_t n_items, double false_positive_rate) {
    assert(false_positive_rate > 0.0 && false_positive_rate < 1.0);
    double ln2 = 0.6931471805599453; // ln(2)
    size_t m = static_cast<size_t>(std::ceil((-static_cast<double>(n_items) * std::log(false_positive_rate)) / (ln2 * ln2)));
    size_t k = static_cast<size_t>(std::ceil((static_cast<double>(m) / static_cast<double>(n_items)) * ln2));
    return BloomParams{m, k};
}

struct SimpleBloom {
    std::vector<uint8_t> storage; // packed bytes
    uint32_t bits;
    uint32_t hash_count;

    SimpleBloom(uint32_t bits_, uint32_t hash_count_) : bits(bits_), hash_count(hash_count_) {
        storage.assign((bits + 7) / 8, 0);
    }

    void set_bit(size_t pos) {
        size_t byte_index = pos / 8;
        size_t bit_index = pos % 8;
        storage[byte_index] |= (1 << bit_index);
    }

    bool get_bit(size_t pos) const {
        size_t byte_index = pos / 8;
        size_t bit_index = pos % 8;
        return (storage[byte_index] & (1 << bit_index)) != 0;
    }

    static uint64_t splitmix64(uint64_t x) {
        x += rand_num;
        x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
        x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL;
        return x ^ (x >> 31);
    }

    void insert(uint32_t value) {
        for (size_t i = 0; i < hash_count; ++i) {
            uint64_t hash = splitmix64(static_cast<uint64_t>(value) + i * rand_num);
            size_t pos = hash % bits;
            set_bit(pos);
        }
    }

    bool might_contain(uint32_t value) const {
        for (size_t i = 0; i < hash_count; ++i) {
            uint64_t hash = splitmix64(static_cast<uint64_t>(value) + i * rand_num);
            size_t pos = hash % bits;
            if (!get_bit(pos)) {
                return false;
            }
        }
        return true;
    }
};

struct CountMinSketch {
    uint32_t width;
    uint32_t depth;
    double base; // base > 1.0 (e.g. 1.08..1.2)
    std::vector<uint32_t> table; // flattened 2D array: depth x width

    CountMinSketch(uint32_t width_, uint32_t depth_) : width(width_), depth(depth_) {
        double error = 0.01;
        double delta = 0.01;
        base = 1.08;
        const double e = 2.71828182845904523536;
        width = static_cast<uint32_t>(std::ceil(e / error));
        depth = static_cast<uint32_t>(std::ceil(std::log(1.0 / delta)));
        if (width < 1) width = 1;
        if (depth < 1) depth = 1;
        table.assign(width * depth, 0);
    }

    static uint64_t hash(uint32_t value, size_t seed) {
        uint64_t x = static_cast<uint64_t>(value) + seed * rand_num;
        return SimpleBloom::splitmix64(x);
    }

    void add(uint32_t value, uint32_t count = 1) {
        for (uint32_t c = 0; c < count; ++c) {
            for (size_t i = 0; i < depth; ++i) {
            uint64_t h = hash(value, i);
            size_t index = h % width;
            size_t pos = i * width + index;
            uint8_t c = table[pos];
            // compute probability
            double p = std::pow(base, -static_cast<int>(c));
            double r = static_cast<double>(rand()) / static_cast<double>(RAND_MAX);
            if (r < p && c < UINT8_MAX) {
                table[pos] = c + 1;
            }
        } 
      }
    }

    uint32_t estimate(uint32_t value) const {
        uint32_t min_estimate = UINT32_MAX;
        for (size_t i = 0; i < depth; ++i) {
            uint64_t h = hash(value, i);
            size_t index = h % width;
            size_t pos = i * width + index;
            uint8_t c = table[pos];
            // inverse morris estimator: (base^c - 1) / (base -1)
            double est = (std::pow(base, static_cast<int>(c)) - 1.0) / (base - 1.0);
            min_estimate = static_cast<uint32_t>(std::ceil(est));
        }
        return min_estimate == UINT32_MAX ? 0 : min_estimate;
    }
};

static void append_bytes(std::vector<std::byte>& buffer, const void* src, size_t size) {
    const std::byte* byte_data = reinterpret_cast<const std::byte*>(src);
    buffer.insert(buffer.end(), byte_data, byte_data + size);
}

std::vector<std::byte> build_idx(std::span<const uint32_t> data, Parameters config){
    size_t budget = (config.f_a * data.size()) / (config.f_s);
    std::unordered_map<uint32_t, uint32_t> freq_map;
    for (const auto &val : data) {
        freq_map[val]++;
    }
    const size_t entry_size = sizeof(uint32_t) + sizeof(uint32_t);
    size_t storage_size = freq_map.size() * entry_size;
    std::vector<std::byte> serialized;
       // header flag : bloom filter + top-k (1)  
        // bloom filter
        size_t remaining_budget = budget;
        size_t bloom_bytes = 0;
        const size_t min_bloom_bytes = 8;
        bloom_bytes = budget / 2;
        remaining_budget -= bloom_bytes;
        // get bloom filter params
        BloomParams bp = bloom_params_for(freq_map.size(), 0.01);
        size_t bloom_bits =  bp.m_bits;
        size_t hash_count =  static_cast<size_t>(bp.k_hashes);
        SimpleBloom bloom{bloom_bits, hash_count};
        for (const auto &key : freq_map) {
                bloom.insert(key.first);
        }

        // pick top-k freq's
        struct Candidate { uint32_t key; size_t count; double net_gain;};
        std::vector<Candidate> candidates;
        candidates.reserve(freq_map.size());
        for (auto &p : freq_map) {
            double benefit = double(p.second) * double(config.f_a);
            double net = benefit - double(entry_size) * double(config.f_s);
            if (net > 0.0) candidates.push_back({p.first, p.second, net});
        }

        //sort by net-gain descending
        std::sort(candidates.begin(), candidates.end(), [](const Candidate& a, const Candidate& b) {
            return a.net_gain > b.net_gain;
        });
        size_t topk_budget = remaining_budget/2;
        std::vector<std::pair<uint32_t, size_t>> topk;
        for (const auto &c : candidates) {
            if (topk_budget < entry_size) break;
            topk.emplace_back(c.key, c.count);
            topk_budget -= entry_size;
        }
        remaining_budget -= topk_budget;

        // size_t max_items = budget / entry_size;
        // std::cout << " budget: " << budget << " max items: " << max_items << std::endl;
        // std::vector<std::pair<uint32_t, size_t>> freq_vec(freq_map.begin(), freq_map.end());
        // std::ptrdiff_t kth = static_cast<std::ptrdiff_t>(std::min(max_items, freq_vec.size()));
        // std::nth_element(freq_vec.begin(), freq_vec.begin() + kth, freq_vec.end(),
        //                  [](const auto &a, const auto &b) {
        //                      return a.second > b.second;
        //                  });
        //top-k entries
       // std::vector<std::pair<uint32_t, size_t>> topk(freq_vec.begin(), freq_vec.begin() + kth);
        
        //compute remaining keys for bloom filter
        // std::vector<uint32_t> remaining_keys;
        // remaining_keys.reserve(freq_vec.size() - topk.size());
        // for (auto it = freq_vec.begin() + kth; it != freq_vec.end(); ++it) {
        //     remaining_keys.push_back(it->first);
        // }
        // size_t overhead = sizeof(uint8_t) + /*flag*/
        //                   sizeof(uint32_t) + /*top-k count*/
        //                   topk.size() * entry_size + /*top-k entries*/
        //                   sizeof(uint32_t) + /*bloom bits*/
        //                   sizeof(uint32_t); /*hash count*/
        
        

        // range index
        // std::unordered_set<uint32_t> chosen_set;
        // chosen_set.reserve(topk.size()*2 + 1);
        // for (auto &e : topk) chosen_set.insert(e.first);

        // uint32_t min_key = UINT32_MAX;
        // uint32_t max_key = 0;
        // for (const auto &key : freq_map) {
        //     if (chosen_set.find(key.first) == chosen_set.end()) {
        //         if (key.first < min_key) min_key = key.first;
        //         if (key.first > max_key) max_key = key.first;
        //     }
        // }
        // RangeIndex rindex{min_key, max_key};

        // count-min sketch
        uint32_t cms_width_height = static_cast<uint32_t>(remaining_budget/4);
        uint32_t cms_width = std::max<uint32_t>(1, 2000);
        uint32_t cms_depth = std::max<uint32_t>(1, 5);
        // std::cout << " CMS dimensions (width x depth): " << cms_width << " x " << cms_depth << std::endl;
        CountMinSketch cms{ cms_width , cms_depth}; // width, depth
        std::unordered_set<uint32_t> chosen_set;
        chosen_set.reserve(topk.size()*2 + 1);
        for (auto &e : topk) chosen_set.insert(e.first);
        // insert keys that were not chosen into top-k
        for (const auto &key : freq_map) {
            if (chosen_set.find(key.first) == chosen_set.end()) {
                uint32_t cnt = key.second;
                cms.add(key.first, cnt);
            }
        }
        size_t cms_table_size = cms.width * cms.depth * sizeof(uint32_t);
        
        // serialize bloom filter index + top-k
        uint8_t flag = 1;
        append_bytes(serialized, &flag, sizeof(flag));
        // serialize bloom filter
        append_bytes(serialized, &bloom.bits, sizeof(bloom.bits));
        append_bytes(serialized, &bloom.hash_count, sizeof(bloom.hash_count));
        append_bytes(serialized, bloom.storage.data(), bloom.storage.size());

        // serialize top-k entries
        uint32_t topk_count = static_cast<uint32_t>(topk.size());
        append_bytes(serialized, &topk_count, sizeof(topk_count));
        for (const auto &p : topk) {
            uint32_t key = p.first;
            uint32_t freq = static_cast<uint32_t>(p.second);
            append_bytes(serialized, &key, sizeof(key));
            append_bytes(serialized, &freq, sizeof(freq));
        }
        
        // serialize range index
        // append_bytes(serialized, &rindex.Min, sizeof(rindex.Min));
        // append_bytes(serialized, &rindex.Max, sizeof(rindex.Max));

        // serialize count-min sketch
        // uint32_t chunk_count = static_cast<uint32_t>(data.size());
        // append_bytes(serialized, &chunk_count, sizeof(chunk_count));
        // append_bytes(serialized, &cms.width, sizeof(cms.width));
        // append_bytes(serialized, &cms.depth, sizeof(cms.depth));
        // append_bytes(serialized, cms.table.data(), cms_table_size);
        return serialized;  
}

std::optional<size_t> query_idx(uint32_t predicate, const std::vector<std::byte>& index){
    size_t offset = 0;
    uint8_t flag;
    std::memcpy(&flag, index.data() + offset, sizeof(flag));
    offset += sizeof(flag);
       // bloom filter + top-k
    //    RangeIndex rindex;
    //    std::memcpy(&rindex.Min, index.data() + offset, sizeof(rindex.Min));
    //    offset += sizeof(rindex.Min);
    //    std::memcpy(&rindex.Max, index.data() + offset, sizeof(rindex.Max));
    //    offset += sizeof(rindex.Max);
    //    if (predicate < rindex.Min || predicate > rindex.Max) {
    //       return 0; // definitely not present
    //    }
       
       
    //    RangeIndex rindex;
    //     std::memcpy(&rindex.Min, index.data() + offset, sizeof(rindex.Min));
    //     offset += sizeof(rindex.Min);
    //     std::memcpy(&rindex.Max, index.data() + offset, sizeof(rindex.Max));
    //     offset += sizeof(rindex.Max);
    //     if (predicate < rindex.Min || predicate > rindex.Max) {
    //         std::cout << " Predicate " << predicate << " outside range index [" << rindex.Min << ", " << rindex.Max << "]" << std::endl;
    //         return 0; // definitely not present   
    //     }

        // bloom filter check
        uint32_t bits;
        uint32_t hash_count;
        std::memcpy(&bits, index.data() + offset, sizeof(bits));
        offset += sizeof(bits);
        std::memcpy(&hash_count, index.data() + offset, sizeof(hash_count));
        offset += sizeof(hash_count);
        size_t bloom_bytes = (bits + 7) / 8;
        SimpleBloom bloom{bits, hash_count};
        std::memcpy(bloom.storage.data(), index.data() + offset, bloom_bytes);
        offset += bloom_bytes;
        if (!bloom.might_contain(predicate)) {
            return 0; // definitely not present
        }

        // top-k check
       uint32_t topk_count;
       std::memcpy(&topk_count, index.data() + offset, sizeof(topk_count));
       offset += sizeof(topk_count);
       for (uint32_t i = 0 ; i < topk_count; ++i) {
         uint32_t key;
         uint32_t freq;
            std::memcpy(&key, index.data() + offset, sizeof(key));
            offset += sizeof(key);
            std::memcpy(&freq, index.data() + offset, sizeof(freq));
            offset += sizeof(freq);
            if (key == predicate) {
                // std::cout << " skip using top-k "<< std::endl;
                return freq;
            }
       }

       // count min sketch
    //    uint32_t chunk_count;
    //    std::memcpy(&chunk_count, index.data() + offset, sizeof(chunk_count));
    //    offset += sizeof(chunk_count);

    //    uint32_t cms_width;
    //    uint32_t cms_depth;
    //    std::memcpy(&cms_width, index.data() + offset, sizeof(cms_width));
    //    offset += sizeof(cms_width);
    //     std::memcpy(&cms_depth, index.data() + offset, sizeof(cms_depth));
    //     offset += sizeof(cms_depth);
    //     CountMinSketch cms{cms_width, cms_depth};
    //     size_t cms_table_size = cms_width * cms_depth * sizeof(uint32_t);
    //     std::memcpy(cms.table.data(), index.data() + offset, cms_table_size);
    //     offset += cms_table_size;
    //     size_t estimate = cms.estimate(predicate);

    //     //compute a conservative acceptance
    //     double econst = 2.71828182845904523536;
    //     double expected_error = 0.0;
    //     if (cms_width > 0) expected_error = (econst / double(cms_width)) * double(chunk_count);
    //     // safety multiplier makes us more conservative (reduce false positives)
    //     const double safety = 1.5;
    //     uint32_t threshold = std::max<uint32_t>(1, static_cast<uint32_t>(std::ceil(expected_error * safety)));
    //     if (estimate > threshold) {
    //         std::cout << " CMS estimate " << estimate << " > threshold " << threshold << " -> skip with estimate" << std::endl;
    //         return estimate;
    //     } 
    return std::nullopt;
}