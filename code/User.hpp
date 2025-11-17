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
#include <functional>

struct RangeIndex {
    uint32_t Min, Max;
};

/*
* SBBF - Split Block Bloom Filter
* A bloom filter variant that splits the bloom filter into multiple blocks
* Each block is a standard bloom filter of 256 bits (8 words of 32 bits
* each). Each block uses 8 hash functions to set/check bits.
* The block to use is selected by multiplying the hash value by the number
* of blocks and taking the top bits.
*/
struct BloomBlock {
    struct BloomMaskResult {
        //8 bit positions in each of the 8 words to set/check
        uint8_t bit_set[8] = {0};
    };

    //bitset vector
    uint32_t block[8] = {0}; // 8 words of 32 bits each = 256 bits

    //set bit i in x
    static void set_bit(uint32_t &x, const uint8_t i) {
       assert ( i < 32);
       x |= (uint32_t) 1 << i;
    }

    //check if bit i is set in x
    static bool check_bit(uint32_t &x, const uint8_t i) {
        assert (i < 32);
        return (x >> i) & (uint32_t)1;
    }

    // find the bit positions to set for each of the 8 hash functions
    static BloomMaskResult Mask(uint32_t x) {
        static const uint32_t bloom_salt[8] = {
            0x47b6137bU, 0x44974d91U, 0x8824ad5bU, 0xa2b7289dU,
            0x705495c7U, 0x2df1424bU, 0x9efc4947U, 0x5c6bfb31U
        };
        BloomMaskResult result;
        //find the 8 words bit positions to set/check
        for (uint8_t i = 0; i < 8; ++i) {
            result.bit_set[i] = (x * bloom_salt[i]) >> 27; // top 5 bits ranging from 0-31
        }
        return result;
    }

    /*
    * Insert x into bloom block
    * Use 8 hash functions to set bits in each of the 8 words
    */
    static void BlockInsert(BloomBlock &b, uint32_t x) {
        auto masked = Mask(x);
        for (size_t i = 0; i < 8; i++)
        {
            set_bit(b.block[i], masked.bit_set[i]);
        }     
    }

    /*
    * Check x in the bloom block
    * Use 8 hash functions to check bits in each of the 8 words are set
    */
    static bool BlockCheck(BloomBlock &b, uint32_t x) {
       auto masked = Mask(x);
       for (size_t i = 0; i < 8; i++)
       {
           if (!check_bit(b.block[i], masked.bit_set[i])) {
               return false;
           }
       }
       return true;
    }
};

struct SimpleBloom {
    static constexpr const uint64_t DEFAULT_BLOCK_COUNT = 32;
    std::vector<BloomBlock> data;
    uint64_t block_count;

    SimpleBloom(uint64_t num_entries, double false_positive_rate) {
       double f = false_positive_rate;
       double k = 8.0;
       double n = num_entries;
       double m = -k * n / std::log(1 - std::pow(f, 1/k));
       auto b = std::max(NextPowerOfTwo(m / k) / 32, 1);
       assert ( b > 0 && IsPowerOfTwo(b));
       block_count = b;
       data.assign(static_cast<size_t>(block_count), BloomBlock{});
    }

    SimpleBloom(std::vector<BloomBlock> &&v) : data(std::move(v)), block_count(data.size()) {}
    
    BloomBlock* blocks() { return data.data();}

    bool IsPowerOfTwo(uint64_t v) {
	    return (v & (v - 1)) == 0;
    }

    int NextPowerOfTwo(uint64_t v) {
        auto v_in = v;
        if (v < 1) { // this is not strictly right but we seem to rely on it in places
            return 2;
        }
        v--;
        v |= v >> 1;
        v |= v >> 2;
        v |= v >> 4;
        v |= v >> 8;
        v |= v >> 16;
        v |= v >> 32;
        v++;
        if (v == 0) {
            std::cout << "Can't find next power of 2 for " << v_in << std::endl;
        }
        return v;
    }

    /*
    * Insert x into bloom filter
    * 64 bit input x
    * Multiply x by block_count and take top bits to select block
    * Use lower 32 bits of x for bloom block insert
    */
    void FilterInsert(uint64_t x) {
        uint64_t i = (x * block_count) >> 32;
        auto &b = data[i];
        return BloomBlock::BlockInsert(b, (uint32_t)x);
    }

    /*
    * Check for x in the bloom filter
    * 64 bit input x
    * Multiply x by block_count and take top bits to select block
    * Use lower 32 bits of x for bloom block check
    */
    bool FilterCheck(uint64_t x) {
        uint64_t i = (x * block_count) >> 32;
        auto &b = data[i];
        return BloomBlock::BlockCheck(b, (uint32_t)x);
    }
};

// append raw bytes to buffer
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

        size_t remaining_budget = budget;
        size_t per_entry_est = 6;
        size_t max_topk = (per_entry_est == 0) ? candidates.size() : std::min(candidates.size(), static_cast<size_t>(std::max<size_t>(1, budget / per_entry_est)));
        // heavy / tail split
        const double heavy_frac = 0.75;
        size_t heavy_count = static_cast<size_t>(std::ceil(max_topk * heavy_frac));
        if (heavy_count > candidates.size()) heavy_count = candidates.size();
        size_t tail_count = max_topk - heavy_count;

        // pick heavy by net gain
        std::vector<std::pair<uint32_t, uint32_t>> topk;
        topk.reserve(max_topk);
        if (!candidates.empty() && heavy_count > 0) {
            if (heavy_count < candidates.size()) {
                std::nth_element(candidates.begin(),
                            candidates.begin() + static_cast<std::ptrdiff_t>(heavy_count),
                            candidates.end(),
                            [](const Candidate &a, const Candidate &b) { return a.net_gain > b.net_gain; });
            }
        }
        for (size_t i = 0; i < heavy_count && i < candidates.size(); ++i) {
            topk.emplace_back(candidates[i].key, candidates[i].count);
        }

        // pick tail 
        if (tail_count > 0) {
            // build vector of keys not already selected
            std::unordered_set<uint32_t> chosen_tmp;
            chosen_tmp.reserve(topk.size()*2 + 1);
            for (auto &e : topk) chosen_tmp.insert(e.first);

            std::vector<std::pair<uint32_t, uint32_t>> tail_candidates;
            tail_candidates.reserve(freq_map.size());
            for (auto &kv : freq_map) {
                if (chosen_tmp.find(kv.first) == chosen_tmp.end()) {
                    tail_candidates.emplace_back(kv.first, kv.second);
                }
            }
            if (!tail_candidates.empty()) {
                if (tail_count < tail_candidates.size()) {
                    std::nth_element(tail_candidates.begin(),
                                tail_candidates.begin() + static_cast<std::ptrdiff_t>(tail_count),
                                tail_candidates.end(),
                                [](const auto &a, const auto &b) { return a.second < b.second; });
                }
            }
            // take up tail_count least frequent keys
            for (size_t i =0; i< tail_count && i < tail_candidates.size(); ++i) {
                topk.emplace_back(tail_candidates[i].first, tail_candidates[i].second);
            }
        }
        remaining_budget -= topk.size() * entry_size;

        std::unordered_set<uint32_t> chosen_set;
        chosen_set.reserve(topk.size()*2 + 1);
        for (auto &e : topk) chosen_set.insert(e.first);

        // bloom filter
        // num of entries to insert into bloom
        auto num_entries = freq_map.size() - chosen_set.size();
        double fp = 0.1; // 10% false positive rate
        SimpleBloom bloom{num_entries, fp};
        for (const auto &key : freq_map) {
            if (chosen_set.find(key.first) == chosen_set.end()) {
                bloom.FilterInsert(static_cast<uint64_t>(key.first));
            }
        }
        uint32_t bloom_len = bloom.data.size() * sizeof(BloomBlock);
        // range index
        uint32_t min_key = UINT32_MAX;
        uint32_t max_key = 0;
        for (const auto &key : freq_map) {
            if (!bloom.FilterCheck(static_cast<uint64_t>(key.first))) continue;
            if (chosen_set.find(key.first) == chosen_set.end()) {
                if (key.first < min_key) min_key = key.first;
                if (key.first > max_key) max_key = key.first;
            }
        }
        RangeIndex rindex{min_key, max_key};

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
        append_bytes(serialized, &bloom_len ,sizeof(bloom_len));
        if (bloom_len > 0) append_bytes(serialized, bloom.data.data(), bloom_len);
        
        // serialize range index
        append_bytes(serialized, &rindex.Min, sizeof(rindex.Min));
        append_bytes(serialized, &rindex.Max, sizeof(rindex.Max));
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
            //std::cout << " Predicate " << predicate << " found in top-k with freq " << freqs[idx] << std::endl;
            return static_cast<size_t>(freqs[idx]);
        }
       }

        // bloom filter check
        uint32_t bloom_len = 0;
        std::memcpy(&bloom_len, index.data() + offset, sizeof(bloom_len));
        offset += sizeof(bloom_len);
        if (bloom_len > 0) {
            size_t bloom_count = bloom_len / sizeof(BloomBlock);
            std::vector<BloomBlock> bloom_blocks;
            bloom_blocks.resize(bloom_count);
            std::memcpy(bloom_blocks.data(), index.data() + offset, bloom_len);
            offset += bloom_len;
            SimpleBloom bloom{std::move(bloom_blocks)};
            if (!bloom.FilterCheck(static_cast<uint64_t>(predicate))) {
                //std::cout<< " Predicate " << predicate << " not in bloom filter" << std::endl;
                return 0; // definitely not present
            }
        }

        RangeIndex rindex;
        std::memcpy(&rindex.Min, index.data() + offset, sizeof(rindex.Min));
        offset += sizeof(rindex.Min);
        std::memcpy(&rindex.Max, index.data() + offset, sizeof(rindex.Max));
        offset += sizeof(rindex.Max);
        if (predicate < rindex.Min || predicate > rindex.Max) {
           //std::cout << " Predicate " << predicate << " outside range index [" << rindex.Min << ", " << rindex.Max << "]" << std::endl;
            return 0; // definitely not present   
        }
    return std::nullopt;
}