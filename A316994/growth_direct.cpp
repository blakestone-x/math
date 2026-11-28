#include <bit>
#include <cstdint>
#include <cstdio>
#include <vector>

// Print the first million terms of A316994, one decimal integer per line.
// Each trial scans the bits of S+x directly for the word of x.
int main() {
    const int limit = 1000000;
    const int pool = 1 << 22;

    // A sorted linked list of the unused integers from 1 to pool-1.
    // Index zero is its head. Start by removing the prescribed first term, 2.
    std::vector<int> next(pool + 1);
    for (int i = 0; i < pool; ++i) {
        next[i] = i + 1;
    }
    next[1] = 3;
    std::uint64_t sum = 2;
    std::printf("2\n");

    for (int step = 2; step <= limit; ++step) {
        int previous = 0;
        bool chosen = false;
        for (int x = next[0]; x < pool && std::uint64_t(x) <= sum;
             previous = x, x = next[x]) {
            const auto mask = (std::uint64_t(1) << std::bit_width(unsigned(x))) - 1;
            for (auto bits = sum + x; bits >= std::uint64_t(x); bits >>= 1) {
                if ((bits & mask) != std::uint64_t(x)) {
                    continue;
                }
                std::printf("%d\n", x);
                next[previous] = next[x];
                sum += x;
                chosen = true;
                break;
            }
            if (chosen) {
                break;
            }
        }
        // Success at every position certifies the search ceiling: every
        // candidate below the chosen x was tested or had already occurred.
        if (!chosen) {
            return 2;
        }
    }
}
