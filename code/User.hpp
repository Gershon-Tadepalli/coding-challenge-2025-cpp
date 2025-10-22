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

const uint64_t rand_num = 0x9e3779b97f4a7c15ULL;

struct RangeIndex {
    uint32_t Min, Max;
};

struct SimpleBloom {
    std::vector<uint8_t> storage; // packed bytes
    uint32_t hash_count;
    uint32_t bits;

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
    // header flag to distinguish full-map (0) vs top-k + bloom + rangeindex (1)
    if (storage_size <= budget) {
        std::cout << " full map " << std::endl;
        uint8_t flag = 0;
        append_bytes(serialized, &flag, sizeof(flag));

        // retain freq map, serialize the index to bytes and return
        uint32_t count = static_cast<uint32_t>(freq_map.size());
        append_bytes(serialized, &count, sizeof(count));
        for (const auto &p : freq_map) {
            uint32_t key = p.first;
            uint32_t freq = static_cast<uint32_t>(p.second);
            append_bytes(serialized, &key, sizeof(key));
            append_bytes(serialized, &freq, sizeof(freq));
        }
        return serialized;
    } 
        std::cout << " top-k + bloom filter " << std::endl;
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

        size_t remaining_budget = budget;
        std::vector<std::pair<uint32_t, size_t>> topk;
        for (const auto &c : candidates) {
            if (remaining_budget < entry_size) break;
            topk.emplace_back(c.key, c.count);
            remaining_budget -= entry_size;
        }
        std::cout << " selected top-k count: " << topk.size() << " remaining budget: " << remaining_budget << std::endl;

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
                            
        size_t bloom_bytes = 0;
        const size_t min_bloom_bytes = 8;
        if (remaining_budget >= min_bloom_bytes) bloom_bytes = remaining_budget;
        if (bloom_bytes == 0) {
            // cannot build bloom filter, fallback to full map
            std::cout << " bloom filter cannot be built, fallback to full map " << std::endl;
            serialized.clear();
            uint8_t flag = 0;
            append_bytes(serialized, &flag, sizeof(flag));
            uint32_t topk_count = static_cast<uint32_t>(topk.size());
            append_bytes(serialized, &topk_count, sizeof(topk_count));
            for (const auto &p : topk) {
                uint32_t key = p.first;
                uint32_t freq = static_cast<uint32_t>(p.second);
                append_bytes(serialized, &key, sizeof(key));
                append_bytes(serialized, &freq, sizeof(freq));
            }
            // bf_bits = 0, hash_count = 0
            uint32_t bf_bits = 0;
            uint32_t bf_hash_count = 0;
            append_bytes(serialized, &bf_bits, sizeof(bf_bits));
            append_bytes(serialized, &bf_hash_count, sizeof(bf_hash_count));
            return serialized;
        }
        size_t bloom_bits = bloom_bytes * 8;
        size_t hash_count = 3;
        SimpleBloom bloom{bloom_bits, hash_count};
        // insert keys that were not chosen into bloom filter
        std::unordered_set<uint32_t> chosen_set;
        chosen_set.reserve(topk.size()*2 + 1);
        for (auto &e : topk) chosen_set.insert(e.first);
        for (const auto &key : freq_map) {
            if (chosen_set.find(key.first) == chosen_set.end()) {
                bloom.insert(key.first);
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

        uint8_t flag = 1;
        // serialize top-k entries + bloom filter index + range index
        append_bytes(serialized, &flag, sizeof(flag));
        uint32_t topk_count = static_cast<uint32_t>(topk.size());
        append_bytes(serialized, &topk_count, sizeof(topk_count));
        for (const auto &p : topk) {
            uint32_t key = p.first;
            uint32_t freq = static_cast<uint32_t>(p.second);
            append_bytes(serialized, &key, sizeof(key));
            append_bytes(serialized, &freq, sizeof(freq));
        }
        append_bytes(serialized, &bloom.bits, sizeof(bloom.bits));
        append_bytes(serialized, &bloom.hash_count, sizeof(bloom.hash_count));
        append_bytes(serialized, bloom.storage.data(), bloom.storage.size());
        append_bytes(serialized, &rindex.Min, sizeof(rindex.Min));
        append_bytes(serialized, &rindex.Max, sizeof(rindex.Max));
        return serialized;  
}

std::optional<size_t> query_idx(uint32_t predicate, const std::vector<std::byte>& index){
    size_t offset = 0;
    uint8_t flag;
    std::memcpy(&flag, index.data() + offset, sizeof(flag));
    offset += sizeof(flag);
    if (flag == 0) {
        //std::cout << " full map index" << std::endl;
        // deserialize and lookup
        uint32_t count;
        std::memcpy(&count, index.data() + offset, sizeof(count));
        offset += sizeof(count);
        for (uint32_t i = 0; i < count; ++i) {
            uint32_t key;
            uint32_t freq;
            std::memcpy(&key, index.data() + offset, sizeof(key));
            offset += sizeof(key);
            std::memcpy(&freq, index.data() + offset, sizeof(freq));
            offset += sizeof(freq);
            if (key == predicate) {
                return freq;
            }

        }
    }
    else {
       // bloom filter + top-k
      // std::cout << " bloom filter + top-k index " << std::endl;
    //    RangeIndex rindex;
    //    std::memcpy(&rindex.Min, index.data() + offset, sizeof(rindex.Min));
    //    offset += sizeof(rindex.Min);
    //    std::memcpy(&rindex.Max, index.data() + offset, sizeof(rindex.Max));
    //    offset += sizeof(rindex.Max);
    //    if (predicate < rindex.Min || predicate > rindex.Max) {
    //       return 0; // definitely not present
    //    }
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
                return freq;
            }
       }
       //bloom filter check
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
       else {
          RangeIndex rindex;
          std::memcpy(&rindex.Min, index.data() + offset, sizeof(rindex.Min));
          offset += sizeof(rindex.Min);
            std::memcpy(&rindex.Max, index.data() + offset, sizeof(rindex.Max));
            offset += sizeof(rindex.Max);
          if (predicate < rindex.Min || predicate > rindex.Max) {
              return 0; // definitely not present   
          }
       }
    }
    return std::nullopt;
}