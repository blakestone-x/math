#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <stdexcept>
#include <vector>

// Each normalized state is its nonnegative balanced ternary value.
// A missing transition either violates the prescribed inner borrow at this
// step, or ends the alternating run before the next step.
void analyze(int pairs) {
    const int width = 1 << pairs;
    const int mask = width - 1;
    int power_of_three = 1;
    for (int i = 0; i < pairs; ++i) power_of_three *= 3;
    const int last = (power_of_three - 1) / 2;

    std::vector<int> ternary(width), reversed(width);
    for (int x = 1; x < width; ++x) {
        ternary[x] = 3 * ternary[x / 2] + x % 2;
        reversed[x] = (reversed[x / 2] >> 1) | ((x % 2) << (pairs - 1));
    }
    std::vector<std::array<int, 2>> successors(last + 1, {-1, -1});
    std::vector<unsigned> indegree(last + 1);
    std::vector<int> digits(pairs);
    int low_difference = 0;
    int high_difference = 0;
    unsigned loops = 0;

    for (int vertex = 0; vertex <= last; ++vertex) {
        for (int borrow = 0; borrow <= 1; ++borrow) {
            if (low_difference < borrow) continue;
            const int low = low_difference - borrow;
            const int high = (width - high_difference) & mask;
            const int next = ternary[reversed[high]] - ternary[low];
            if (next < 0) continue;
            successors[vertex][borrow] = next;
            if (next == vertex) {
                if (borrow != int(high_difference > 0))
                    throw std::logic_error("self-loop has unequal outer borrows");
                ++loops;
            } else {
                ++indegree[next];
            }
        }
        // Increment the balanced ternary digits while updating their two
        // binary-weighted sums. The lowest index is the outermost pair.
        if (vertex == last) break;
        for (int i = 0; i < pairs; ++i) {
            const int delta = digits[i] == 1 ? -2 : 1;
            digits[i] += delta;
            low_difference += delta * (1 << i);
            high_difference += delta * (1 << (pairs - 1 - i));
            if (delta == 1) break;
        }
    }

    std::vector<int> order;
    order.reserve(last + 1);
    for (int v = 0; v <= last; ++v) {
        if (indegree[v] == 0) order.push_back(v);
    }
    std::vector<std::uint16_t> marked_before(last + 1), edges_before(last + 1);
    int max_marked = 0;
    int max_edges = 0;
    for (std::size_t i = 0; i < order.size(); ++i) {
        const int v = order[i];
        const bool marked = successors[v][0] == v || successors[v][1] == v;
        const int marked_through = marked_before[v] + int(marked);
        max_marked = std::max(max_marked, marked_through);
        max_edges = std::max(max_edges, int(edges_before[v]));
        for (const int w : successors[v]) {
            if (w < 0 || w == v) continue;
            if (marked_through > UINT16_MAX || edges_before[v] == UINT16_MAX)
                throw std::overflow_error("path length exceeds storage");
            marked_before[w] = std::max<int>(marked_before[w], marked_through);
            edges_before[w] = std::max<int>(edges_before[w], edges_before[v] + 1);
            if (--indegree[w] == 0) order.push_back(w);
        }
    }
    if (order.size() != std::size_t(last + 1) || loops != unsigned(width))
        throw std::logic_error("cycle or unexpected self-loop count");
    std::cout << pairs << ' ' << last + 1 << ' ' << loops << ' '
              << max_marked << ' ' << max_edges << std::endl;
}

int main(int argc, char** argv) {
    const int last = argc == 2 ? std::atoi(argv[1]) : 12;
    if (argc > 2 || last < 1 || last > 18) {
        std::cerr << "usage: shells [maximum block width, 1 through 18]\n";
        return 2;
    }
    for (int k = 1; k <= last; ++k) analyze(k);
}
