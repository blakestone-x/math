#define main proof_checker_main
#include "forest_verify.cpp"
#undef main
#include <random>

// Exhaust endpoint subsets, independently checking induced acyclicity by component unions
// and then perfect matchability by taking the least-indexed unmatched vertex.
static bool perfect(const Graph &g, unsigned selected) {
    if (!selected)
        return true;
    const int i = __builtin_ctz(selected);
    for (int j = i + 1; j < g.n; ++j)
        if ((selected >> j & 1U) && g.a[i][j] == 1 && perfect(g, selected ^ (1U << i) ^ (1U << j)))
            return true;
    return false;
}
static int brute(const Graph &g) {
    int best = 0;
    for (unsigned mask = 1; mask < (1U << g.n); ++mask) {
        int vertices = __builtin_popcount(mask);
        if ((vertices & 1) || vertices <= 2 * best)
            continue;
        std::vector<int> labels(g.n);
        std::iota(labels.begin(), labels.end(), 0);
        bool ok = true;
        for (int i = 0; i < g.n && ok; ++i) {
            if (!(mask >> i & 1U))
                continue;
            if (g.a[i][i] || g.weight[i] != 1) {
                ok = false;
                break;
            }
            for (int j = i + 1; j < g.n && ok; ++j) {
                if (!(mask >> j & 1U) || g.a[i][j] == 0)
                    continue;
                if (g.a[i][j] > 1 || labels[i] == labels[j]) {
                    ok = false;
                    break;
                }
                const int old = labels[j], to = labels[i];
                for (int &l : labels)
                    if (l == old)
                        l = to;
            }
        }
        if (ok && perfect(g, mask))
            best = vertices / 2;
    }
    return best;
}
static long long tests = 0, graphs = 0;
static void check(const Graph &g) {
    int b = brute(g);
    ++graphs;
    for (int m = 0; m <= g.n / 2 + 1; ++m) {
        assert(g.has_forest_matching(m) == (m <= b));
        ++tests;
    }
}
int main() {
    for (int n = 2; n <= 6; ++n) {
        for (int code = 0; code < 1 << (n * (n - 1) / 2); ++code) {
            Graph g(n);
            int index = 0;
            for (int i = 0; i < n; ++i)
                for (int j = i + 1; j < n; ++j)
                    if (code >> index++ & 1)
                        g.add(i, j);
            check(g);
        }
    }
    std::mt19937 generator(20261126);
    for (int iter = 0; iter < 12000; ++iter) {
        int n = 2 + generator() % 10;
        Graph g(n);
        for (int i = 0; i < n; ++i) {
            if (generator() % 8 == 0)
                g.weight[i] = 2 + generator() % 5;
            if (generator() % 16 == 0)
                g.add(i, i);
            for (int j = i + 1; j < n; ++j)
                if (generator() % 7 < 2) {
                    g.add(i, j);
                    if (generator() % 6 == 0)
                        g.add(i, j);
                }
        }
        check(g);
    }
    std::cout << graphs << " graphs and " << tests << " target matching sizes agree.\n";
}
