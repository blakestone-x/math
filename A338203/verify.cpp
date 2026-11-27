// Exact enumeration of signed mirror-pair states for binary reverse subtraction.
// Build with c++ -O3 -std=c++17 verify.cpp -o verify ; run ./verify 18
#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

using Word = std::uint64_t;
using Index = std::uint32_t;

class MirrorStates {
    unsigned m;
    Word mask;
    std::vector<Index> pow3, weight, reversed;
    Index split;
    std::vector<Word> outer, inner;

    // Store the signed contribution of each block directly to x - rev(x).
    std::vector<Word> block(unsigned start, unsigned length) const {
        std::vector<Word> values(pow3[length]);
        for (unsigned j = 0; j < length; ++j) {
            unsigned i = start + j;
            Word delta = (Word{1} << i) - (Word{1} << (2 * m - 1 - i));
            for (Index k = 0; k < pow3[j]; ++k) {
                values[k + pow3[j]] = values[k] + delta;
                values[k + 2 * pow3[j]] = values[k] - delta;
            }
        }
        return values;
    }

public:
    explicit MirrorStates(unsigned pairs) : m(pairs), mask((Word{1} << (2 * m)) - 1),
        pow3(m + 1, 1), weight(1u << m), reversed(1u << m) {
        for (unsigned i = 0; i < m; ++i) pow3[i + 1] = 3 * pow3[i];
        for (Index k = 1; k < (1u << m); ++k) {
            unsigned i = 0;
            for (Index v = k; !(v & 1); v >>= 1) ++i;
            weight[k] = weight[k & (k - 1)] + pow3[i];
            reversed[k] = (reversed[k >> 1] >> 1) | ((k & 1) << (m - 1));
        }
        split = pow3[m / 2];
        outer = block(0, m / 2);
        inner = block(m / 2, m - m / 2);
    }

    Index size() const { return pow3[m]; }

    Index next(Index state) const {
        Word y = (outer[state % split] + inner[state / split]) & mask;
        Index low = static_cast<Index>(y) & ((1u << m) - 1);
        Index high = reversed[y >> m];
        return weight[low & ~high] + 2 * weight[high & ~low];
    }

    Word representative(Index state) const {
        Word x = 0;
        for (unsigned i = 0; i < m; ++i, state /= 3) {
            if (state % 3 == 1) x |= Word{1} << i;
            if (state % 3 == 2) x |= Word{1} << (2 * m - 1 - i);
        }
        return x;
    }
};

void verify(unsigned m) {
    MirrorStates states(m);
    // 0 = unseen, 255 = on this path, other bytes = 1 + distance to zero.
    constexpr unsigned active = 255;
    std::vector<std::uint8_t> label(states.size());
    std::vector<Index> path;
    label[0] = 1;
    unsigned maximum = 0;
    Index extremizer = 0;
    for (Index start = 1; start < states.size(); ++start) {
        if (label[start]) continue;
        path.clear();
        Index v = start;
        while (!label[v]) {
            label[v] = active;
            path.push_back(v);
            v = states.next(v);
        }
        if (label[v] == active) throw std::runtime_error("nonzero cycle at state " + std::to_string(v));
        unsigned distance = label[v] - 1;
        for (auto it = path.rbegin(); it != path.rend(); ++it) {
            ++distance;
            if (distance + 1 >= active) throw std::runtime_error("distance exceeds label capacity");
            label[*it] = static_cast<std::uint8_t>(distance + 1);
            if (distance > maximum) { maximum = distance; extremizer = *it; }
        }
    }
    std::cout << m << ' ' << states.size() << ' ' << maximum << ' ' << states.representative(extremizer) << std::endl;
}

int main(int argc, char** argv) {
    try {
        int first = argc == 3 ? std::stoi(argv[1]) : 1;
        int last = argc > 1 ? std::stoi(argv[argc - 1]) : 12;
        if (argc > 3 || first < 1 || last < first || last > 20) throw std::runtime_error("usage: verify [first] [last], 1 <= first <= last <= 20");
        std::cout << "pairs states maximum witness" << std::endl;
        for (int m = first; m <= last; ++m) verify(static_cast<unsigned>(m));
    } catch (const std::exception& e) { std::cerr << e.what() << '\n'; return EXIT_FAILURE; }
}
