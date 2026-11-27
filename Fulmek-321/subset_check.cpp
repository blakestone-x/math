// Direct subset dynamic program for decreasing triples, independent of the path proof.
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <vector>

constexpr unsigned modulus = 47;
constexpr unsigned largest_count = 8;
using Counts = std::array<std::uint8_t, largest_count + 1>;

Counts count_by_subsets(unsigned n) {
    const std::uint32_t end = std::uint32_t{1} << n;
    const std::uint32_t full = end - 1;
    std::vector<Counts> ways(end);
    ways[0][0] = 1;
    for (std::uint32_t used = 0; used < full; ++used) {
        std::uint32_t available = full ^ used;
        unsigned smaller_remaining = 0;
        while (available) {
            const std::uint32_t bit = available & -available;
            available ^= bit;
            const unsigned larger_used = std::popcount(used & ~(bit | (bit - 1)));
            const unsigned cost = larger_used * smaller_remaining;
            ++smaller_remaining;
            if (cost > largest_count) continue;
            Counts &next = ways[used | bit];
            const Counts &current = ways[used];
            for (unsigned r = cost; r <= largest_count; ++r) {
                const unsigned total = next[r] + current[r - cost];
                next[r] = static_cast<std::uint8_t>(total >= modulus ? total - modulus : total);
            }
        }
    }
    return ways[full];
}

int main() {
    for (unsigned n = 0; n <= 25; ++n) {
        const auto counts = count_by_subsets(n);
        std::cout << n;
        for (const auto value : counts) std::cout << ' ' << static_cast<unsigned>(value);
        std::cout << '\n';
    }
}
