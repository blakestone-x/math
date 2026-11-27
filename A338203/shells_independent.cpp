// Independent low-memory verifier for the alternating-borrow block bounds.
// c++ -O3 -std=c++17 shells_independent.cpp -o shells_independent
// ./shells_independent 18             # Check one selected number of pairs.
//
// Visit the normalized balanced-ternary states by a depth-first search. A
// transition is reconstructed when its source is first visited. The two-byte
// memo stores both longest-path statistics and the two DFS status sentinels.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>

struct Chunk {
    int binary_radix = 1;
    int ternary_radix = 1;
    std::vector<int> forward_difference, reversed_difference;
    std::vector<int> ternary_bits, reversed_ternary_bits;

    explicit Chunk(int length) {
        for (int i = 0; i < length; ++i) {
            binary_radix *= 2;
            ternary_radix *= 3;
        }
        forward_difference.resize(ternary_radix);
        reversed_difference.resize(ternary_radix);
        for (int code = 0; code < ternary_radix; ++code) {
            int t = code;
            for (int i = 0; i < length; ++i) {
                // code represents ordinary ternary digits 0,1,2; subtract 1
                // from each digit to get the corresponding signed difference.
                const int digit = t % 3 - 1;
                t /= 3;
                forward_difference[code] += digit * (1 << i);
                reversed_difference[code] += digit * (1 << (length-1-i));
            }
        }
        ternary_bits.resize(binary_radix);
        reversed_ternary_bits.resize(binary_radix);
        for (int bits = 0; bits < binary_radix; ++bits) {
            int weight = 1;
            for (int i = 0; i < length; ++i) {
                if ((bits >> i) & 1) ternary_bits[bits] += weight;
                if ((bits >> (length-1-i)) & 1) reversed_ternary_bits[bits] += weight;
                weight *= 3;
            }
        }
    }
};

class ShellAudit {
    static constexpr std::uint16_t unseen = 65535;
    static constexpr std::uint16_t active = 65534;
    static constexpr int edge_bits = 9;
    static constexpr int edge_mask = (1 << edge_bits)-1;

    int pairs;
    Chunk outer, inner;
    int binary_modulus;
    int last_vertex;
    std::vector<std::uint16_t> memo;
    std::uint64_t loop_total = 0;
    int max_marked = 0, max_edges = 0;

    void visit(int vertex) {
        const std::uint16_t current = memo[vertex];
        if (current == active) throw std::runtime_error("cycle traversing unequal states");
        if (current != unseen) return;
        memo[vertex] = active;

        // Adding last_vertex adds one to every balanced digit. At twenty
        // pairs the sum exceeds a signed 32-bit integer, although each vertex
        // index, binary weighted sum, and T(bit word) separately fits in one.
        const auto code = std::uint64_t(vertex) + last_vertex;
        const int lo = int(code % outer.ternary_radix);
        const int hi = int(code / outer.ternary_radix);
        const int low_difference = outer.forward_difference[lo]
                                 + outer.binary_radix * inner.forward_difference[hi];
        const int high_difference = inner.binary_radix * outer.reversed_difference[lo]
                                  + inner.reversed_difference[hi];
        const int high = (binary_modulus - high_difference) & (binary_modulus-1);
        const int high_ternary = outer.reversed_ternary_bits[high / inner.binary_radix]
                       + outer.ternary_radix * inner.reversed_ternary_bits[high % inner.binary_radix];

        bool loop = false;
        int descendant_marks = 0, edges = 0;
        for (int borrow = 0; borrow <= 1; ++borrow) {
            const int low = low_difference - borrow;
            if (low < 0) continue;
            const int low_ternary = outer.ternary_bits[low % outer.binary_radix]
                       + outer.ternary_radix * inner.ternary_bits[low / outer.binary_radix];
            const int next = high_ternary - low_ternary;
            if (next < 0) continue;
            if (next == vertex) {
                if (loop || borrow != int(high_difference > 0))
                    throw std::runtime_error("self-loop violates the outer-borrow condition");
                loop = true;
                continue;
            }
            visit(next);
            const std::uint16_t child = memo[next];
            descendant_marks = std::max(descendant_marks, int(child >> edge_bits));
            edges = std::max(edges, 1 + int(child & edge_mask));
        }
        const int marks = descendant_marks + int(loop);
        if (marks >= (1 << (16-edge_bits)) || edges > edge_mask)
            throw std::overflow_error("longest path exceeds memo capacity");
        const int packed = (marks << edge_bits) | edges;
        if (packed >= active) throw std::overflow_error("memo sentinel collision");
        memo[vertex] = std::uint16_t(packed);
        loop_total += int(loop);
        max_marked = std::max(max_marked, marks);
        max_edges = std::max(max_edges, edges);
    }

public:
    explicit ShellAudit(int width)
        : pairs(width), outer(width/2), inner(width-width/2),
          binary_modulus(1 << width),
          last_vertex(int((std::uint64_t(outer.ternary_radix)*inner.ternary_radix-1)/2)),
          memo(std::size_t(last_vertex)+1, unseen) {}

    void run() {
        for (int v = 0; v <= last_vertex; ++v) visit(v);
        if (loop_total != std::uint64_t(binary_modulus))
            throw std::runtime_error("unexpected self-loop count");
        std::cout << pairs << ' ' << memo.size() << ' ' << loop_total << ' '
                  << max_marked << ' ' << max_edges << '\n';
    }
};

int main(int argc, char **argv) {
    const std::string arg = argc == 2 ? argv[1] : "18";
    std::size_t used = 0;
    const int width = std::stoi(arg, &used);
    if (argc > 2 || used != arg.size() || width < 1 || width > 20) {
        std::cerr << "usage: shells_independent [number of pairs, 1 through 20]\n";
        return 2;
    }
    ShellAudit(width).run();
}
