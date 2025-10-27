#include <optional>
#include <vector>
#include <span>
#include <cstdint>
#include <cassert>
#include <algorithm>
#include <cstring>

#include "Parameters.hpp"
#include "FileUtils.hpp"
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
    if ( k > 3) k = 3; // cap at 8 hash functions
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

    // insert using double hashing: (h1 + i * h2) mod m
    void insert(uint32_t value) {
        if (bits == 0) return;
        uint64_t h1 = splitmix64(static_cast<uint64_t>(value));
        uint64_t h2 = splitmix64(static_cast<uint64_t>(value ^ 0x9e3779b97f4a7c15ULL));
        for (size_t i = 0; i < hash_count; ++i) {
            uint64_t combined = h1 + static_cast<uint64_t>(i) * h2;
            size_t pos = combined % bits;
            set_bit(pos);
        }
    }

    bool might_contain(uint32_t value) const {
        if (bits == 0) return true;
        uint64_t h1 = splitmix64(static_cast<uint64_t>(value));
        uint64_t h2 = splitmix64(static_cast<uint64_t>(value ^ 0x9e3779b97f4a7c15ULL));
        for (size_t i = 0; i < hash_count; ++i) {
            uint64_t combined = h1 + static_cast<uint64_t>(i) * h2;
            size_t pos = combined % bits;
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

static void write_varuint32(std::vector<std::byte>& out, uint32_t v) {
    while (v >= 0x80u) {
        uint8_t b = static_cast<uint8_t>((v & 0x7Fu) | 0x80u);
        out.push_back(static_cast<std::byte>(b));
        v >>= 7;
    }
    out.push_back(static_cast<std::byte>(static_cast<uint8_t>(v)));
}

// varint read for uint32; returns false on overflow/out-of-bounds
static bool read_varuint32(const std::vector<std::byte>& in, size_t& offset, uint32_t& value) {
    uint32_t result = 0;
    unsigned shift = 0;
    while (offset < in.size()) {
        uint8_t byte = static_cast<uint8_t>(in[offset]);
        ++offset;
        result |= static_cast<uint32_t>(byte & 0x7Fu) << shift;
        if ((byte & 0x80u) == 0) {
            value = result;
            return true;
        }
        shift += 7;
        if (shift >= 35) return false; // too large
    }
    return false;
}

std::vector<std::byte> build_idx(std::span<const uint32_t> data, Parameters config){
        size_t budget = (static_cast<size_t>(config.f_a) * data.size()) / (config.f_s);
        std::unordered_map<uint32_t, uint32_t> freq_map;
        for (const auto &val : data) {
            freq_map[val]++;
        }
        const size_t entry_size = sizeof(uint32_t) + sizeof(uint32_t); // key + freq
        size_t storage_size = freq_map.size() * entry_size;
        std::vector<std::byte> serialized;

        // header flag + bloom filter + top-k + range index

        // pick top-k freq's
        struct Candidate { uint32_t key; uint32_t count; double net_gain;};
        std::vector<Candidate> candidates;
        candidates.reserve(freq_map.size());
        for (auto &p : freq_map) {
            double benefit = double(p.second * p.second) * double(config.f_a);
            double net = benefit - double(entry_size) * double(config.f_s);
            if (net > 0.0) candidates.push_back({p.first, p.second, net});
        }

        //sort by net-gain descending
        std::sort(candidates.begin(), candidates.end(), [](const Candidate& a, const Candidate& b) {
            return a.net_gain > b.net_gain;
        });
        size_t remaining_budget = budget;
        size_t per_entry_est = 6;
        size_t max_topk = (per_entry_est == 0) ? candidates.size() : std::min(candidates.size(), static_cast<size_t>(std::max<size_t>(1, budget / per_entry_est)));
        std::vector<std::pair<uint32_t, uint32_t>> topk;
        topk.reserve(max_topk);
        for (size_t i = 0; i < max_topk && i < candidates.size(); ++i) {
            topk.emplace_back(candidates[i].key, candidates[i].count);
        }
        remaining_budget -= topk.size() * entry_size;

        std::unordered_set<uint32_t> chosen_set;
        chosen_set.reserve(topk.size()*2 + 1);
        for (auto &e : topk) chosen_set.insert(e.first);

        // bloom filter
        size_t bloom_bytes = 0;
        const size_t min_bloom_bytes = 8;
        if (remaining_budget >= min_bloom_bytes) {
             bloom_bytes = std::min(remaining_budget, std::max(min_bloom_bytes, remaining_budget/2));
        }
        remaining_budget -= bloom_bytes;
        // get bloom filter params
        BloomParams bp = bloom_params_for(freq_map.size() - chosen_set.size(), 0.6); // target 60% false-positive rate
        size_t bloom_bits =  bp.m_bits;
        size_t hash_count =  static_cast<size_t>(bp.k_hashes);
        SimpleBloom bloom{bloom_bits, hash_count};
        if (bloom.bits > 0){
            for (const auto &key : freq_map) {
                if (chosen_set.find(key.first) == chosen_set.end()) {
                    bloom.insert(key.first);
                }
            }
        }
        // range index
        uint32_t min_key = UINT32_MAX;
        uint32_t max_key = 0;
        for (const auto &key : freq_map) {
            if (chosen_set.find(key.first) == chosen_set.end()) {
                if (key.first < min_key) min_key = key.first;
                if (key.first > max_key) max_key = key.first;
            }
        }
        RangeIndex rindex{min_key, max_key};
        //std::cout << " range index min: " << rindex.Min << " max: " << rindex.Max << std::endl;

        // count-min sketch
        // uint32_t cms_width_height = static_cast<uint32_t>(remaining_budget/4);
        // uint32_t cms_width = std::max<uint32_t>(1, 2000);
        // uint32_t cms_depth = std::max<uint32_t>(1, 5);
        // // std::cout << " CMS dimensions (width x depth): " << cms_width << " x " << cms_depth << std::endl;
        // CountMinSketch cms{ cms_width , cms_depth}; // width, depth
        // std::unordered_set<uint32_t> chosen_set;
        // chosen_set.reserve(topk.size()*2 + 1);
        // for (auto &e : topk) chosen_set.insert(e.first);
        // // insert keys that were not chosen into top-k
        // for (const auto &key : freq_map) {
        //     if (chosen_set.find(key.first) == chosen_set.end()) {
        //         uint32_t cnt = key.second;
        //         cms.add(key.first, cnt);
        //     }
        // }
        // size_t cms_table_size = cms.width * cms.depth * sizeof(uint32_t);
        
        // serialize layout:
        // [topk_count:uint32][topk keys (delta+varint)][topk freqs (varint sequence)] |[bloom_bits:uint32][bloom_hash:uint32][bloom bytes..] | [range.Min,range.Max] (8 bytes) |

        // serialize top-k : sort ascending keys and delta+varint encode
        std::sort(topk.begin(), topk.end(), [](const auto &a, const auto &b){ return a.first < b.first; });
        uint32_t topk_count = static_cast<uint32_t>(topk.size());
        append_bytes(serialized, &topk_count, sizeof(topk_count));
        if (topk_count > 0) {
            // write first key raw [4 bytes] then deltas as varints
            uint32_t first_key = topk[0].first;
            append_bytes(serialized, &first_key, sizeof(first_key));
            for (size_t i = 1; i < topk.size(); ++i) {
                uint32_t delta = topk[i].first - topk[i-1].first;
                write_varuint32(serialized, delta);
            }
            //write freqs as varints
            for (size_t i = 0; i < topk.size(); ++i){
                write_varuint32(serialized, topk[i].second);
            }
        }
        // serialize bloom filter
        append_bytes(serialized, &bloom.bits, sizeof(bloom.bits));
        append_bytes(serialized, &bloom.hash_count, sizeof(bloom.hash_count));
        if (bloom.bits > 0) append_bytes(serialized, bloom.storage.data(), bloom.storage.size());
        
        // serialize range index
        append_bytes(serialized, &rindex.Min, sizeof(rindex.Min));
        append_bytes(serialized, &rindex.Max, sizeof(rindex.Max));

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
       // bloom filter + top-k + range index
       // top-k check
       uint32_t topk_count;
       std::memcpy(&topk_count, index.data() + offset, sizeof(topk_count));
       offset += sizeof(topk_count);

       std::vector<uint32_t> keys;
       keys.reserve(topk_count);
       if (topk_count > 0) {
         if (offset + sizeof(uint32_t) > index.size()) return std::nullopt;
         uint32_t first_key;
         std::memcpy(&first_key, index.data() + offset, sizeof(first_key));
         offset += sizeof(first_key);
         keys.push_back(first_key);
         for (uint32_t i = 1; i < topk_count; ++i) {
            uint32_t delta;
            if (!read_varuint32(index, offset, delta)) return std::nullopt;
            keys.push_back(keys.back() + delta);
         }
         // read freqs
         std::vector<uint32_t> freqs;
         freqs.reserve(topk_count);
         for (uint32_t i = 0; i < topk_count; ++i) {
            uint32_t f;
            if (!read_varuint32(index, offset, f)) return std::nullopt;
            freqs.push_back(f);
         }
         // search for predicate in keys
        auto it = std::lower_bound(keys.begin(), keys.end(), predicate);
        if (it != keys.end() && *it == predicate) {
            size_t idx = static_cast<size_t>(it - keys.begin());
            return static_cast<size_t>(freqs[idx]);
        }
       }

        // bloom filter check
        uint32_t bits;
        uint32_t hash_count;
        std::memcpy(&bits, index.data() + offset, sizeof(bits));
        offset += sizeof(bits);
        std::memcpy(&hash_count, index.data() + offset, sizeof(hash_count));
        offset += sizeof(hash_count);
        if (bits > 0) {
            size_t bloom_bytes = (bits + 7) / 8;
            SimpleBloom bloom{bits, hash_count};
            std::memcpy(bloom.storage.data(), index.data() + offset, bloom_bytes);
            offset += bloom_bytes;
            if (!bloom.might_contain(predicate)) {
                return 0; // definitely not present
            }
        }

        RangeIndex rindex;
        std::memcpy(&rindex.Min, index.data() + offset, sizeof(rindex.Min));
        offset += sizeof(rindex.Min);
        std::memcpy(&rindex.Max, index.data() + offset, sizeof(rindex.Max));
        offset += sizeof(rindex.Max);
        if (predicate < rindex.Min || predicate > rindex.Max) {
           // std::cout << " Predicate " << predicate << " outside range index [" << rindex.Min << ", " << rindex.Max << "]" << std::endl;
            return 0; // definitely not present   
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