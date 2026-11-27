// Exact branch-form certificate. Compile with a C++17 compiler, GMP and GMPXX.
#ifdef NDEBUG
#error Assertions must be enabled.
#endif
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <gmpxx.h>
#include <iostream>
#include <numeric>
#include <set>
#include <string>
#include <utility>
#include <vector>

namespace {
constexpr int limit = 32;
using Edge = std::pair<int, int>;
using Matrix = std::array<std::array<int, limit>, limit>;
using Bits = unsigned;
Bits bit(int v) { return 1U << v; }
struct Graph {
    int n = 0;
    Matrix a{};
    std::array<int, limit> degree{}, weight{};
    std::array<Bits, limit> neighbors{};
    std::vector<Edge> edges;
    explicit Graph(int order = 0) : n(order) { weight.fill(1); }
    void add(int u, int v) {
        if (u > v)
            std::swap(u, v);
        edges.emplace_back(u, v);
        ++a[u][v];
        ++degree[u];
        ++degree[v];
        if (u != v) {
            ++a[v][u];
            neighbors[u] |= bit(v);
            neighbors[v] |= bit(u);
        }
    }
    struct Pair {
        Bits inside, outside, bad;
    };
    bool extend(const std::vector<Pair> &pairs, int first, Bits vertices,
                const std::array<Bits, 8> &components, int count, int needed) const {
        if (!needed)
            return true;
        for (int i = first; i + needed <= int(pairs.size()); ++i) {
            const auto &p = pairs[i];
            if (vertices & (p.inside | p.bad))
                continue;
            std::array<Bits, 8> next{};
            int ncomp = 0;
            Bits joined = p.inside;
            bool cycle = false;
            for (int j = 0; j < count; ++j) {
                Bits adjacent = components[j] & p.outside;
                if (adjacent & (adjacent - 1)) {
                    cycle = true;
                    break;
                }
                if (adjacent)
                    joined |= components[j];
                else
                    next[ncomp++] = components[j];
            }
            if (cycle)
                continue;
            next[ncomp++] = joined;
            if (extend(pairs, i + 1, vertices | p.inside, next, ncomp, needed - 1))
                return true;
        }
        return false;
    }
    bool has_forest_matching(int size) const {
        std::array<Bits, limit> multi{};
        for (auto [i, j] : edges)
            if (i != j && a[i][j] > 1) {
                multi[i] |= bit(j);
                multi[j] |= bit(i);
            }
        std::vector<Pair> pairs;
        for (auto [i, j] : edges)
            if (i != j && a[i][j] == 1 && !a[i][i] && !a[j][j] && weight[i] == 1 && weight[j] == 1) {
                Bits inside = bit(i) | bit(j);
                pairs.push_back({inside, (neighbors[i] | neighbors[j]) & ~inside,
                                 multi[i] | multi[j] | (neighbors[i] & neighbors[j])});
            }
        return extend(pairs, 0, 0, {}, 0, size);
    }
    std::string key() const {
        std::string s;
        for (int i = 0; i < n; ++i) {
            s += char(weight[i]);
            for (int j = i; j < n; ++j)
                s += char(a[i][j]);
        }
        return s;
    }
};
int J = 0, budget = 3;
bool emit_only = false, found = false, strict = false;
long long exceptions = 0;
std::array<long long, 8> strict_domains{}, strict_forms{};
long long input_count = 0, cubic_count = 0;
std::array<long long, 8> domains{}, forms{}, violations{};

Graph read(const std::string &s) {
    int n = int(s.at(0)) - 63;
    assert(n > 1 && n < limit);
    assert(int(s.size()) == 1 + (n * (n - 1) / 2 + 5) / 6);
    Graph g(n);
    int k = 0;
    for (int j = 1; j < n; ++j)
        for (int i = 0; i < j; ++i, ++k)
            if ((int(s[1 + k / 6]) - 63) & (32 >> (k % 6)))
                g.add(i, j);
    return g;
}
// Characteristic polynomial and sign variations of p(x),p(-x).  For an
// integer symmetric matrix every root is real, making Descartes' counts exact.
int characteristic_deficit(const Matrix &a, int n) {
    using Big = std::array<std::array<mpz_class, limit>, limit>;
    Big b{}, next{};
    int last_pos = 1, last_neg = 1, pos = 0, neg = 0;
    for (int i = 0; i < n; ++i)
        b[i][i] = 1;
    for (int k = 1; k <= n; ++k) {
        for (int i = 0; i < n; ++i)
            for (int j = 0; j < n; ++j)
                next[i][j] = 0;
        for (int i = 0; i < n; ++i)
            for (int j = 0; j < n; ++j)
                if (a[i][j])
                    for (int h = 0; h < n; ++h)
                        next[i][h] += a[i][j] * b[j][h];
        mpz_class tr = 0;
        for (int i = 0; i < n; ++i)
            tr += next[i][i];
        assert(tr % k == 0);
        mpz_class coefficient = -tr / k;
        int sp = sgn(coefficient), sn = (k & 1) ? -sp : sp;
        if (sp) {
            pos += (sp != last_pos);
            neg += (sn != last_neg);
            last_pos = sp;
            last_neg = sn;
        }
        for (int i = 0; i < n; ++i)
            next[i][i] += coefficient;
        b.swap(next);
    }
    return n - pos + neg;
}
// Exact symmetric congruence, removing a scalar pivot or a zero-diagonal
// hyperbolic pair. Normalize each Schur complement by its positive content.
int exact_deficit(const Matrix &a, int n) {
    using Big = std::vector<std::vector<mpz_class>>;
    Big b(n, std::vector<mpz_class>(n));
    for (int i = 0; i < n; ++i)
        for (int j = 0; j < n; ++j)
            b[i][j] = a[i][j];
    int loss = 0;
    while (!b.empty()) {
        int l = b.size(), u = -1, v = -1;
        for (int i = 0; i < l; ++i)
            if (b[i][i] != 0) {
                u = i;
                break;
            }
        if (u < 0) {
            for (int i = 0; u < 0 && i < l; ++i)
                for (int j = i + 1; j < l; ++j)
                    if (b[i][j] != 0) {
                        u = i;
                        v = j;
                        break;
                    }
        }
        if (u < 0) {
            loss += l;
            break;
        }
        bool pair = v >= 0;
        mpz_class z = pair ? b[u][v] : b[u][u];
        int sign = sgn(z);
        mpz_class abs_z = abs(z);
        loss += pair ? 2 : (sign < 0 ? 2 : 0);
        std::vector<int> keep;
        for (int i = 0; i < l; ++i)
            if (i != u && i != v)
                keep.push_back(i);
        int m = keep.size();
        Big next(m, std::vector<mpz_class>(m));
        mpz_class content = 0;
        for (int i = 0; i < m; ++i)
            for (int j = i; j < m; ++j) {
                int x = keep[i], y = keep[j];
                mpz_class correction;
                if (pair)
                    correction = b[x][u] * b[v][y] + b[x][v] * b[u][y];
                else
                    correction = b[x][u] * b[u][y];
                next[i][j] = abs_z * b[x][y] - sign * correction;
                mpz_gcd(content.get_mpz_t(), content.get_mpz_t(), next[i][j].get_mpz_t());
            }
        if (content == 0) {
            loss += m;
            break;
        }
        for (int i = 0; i < m; ++i)
            for (int j = i; j < m; ++j) {
                next[i][j] /= content;
                next[j][i] = next[i][j];
            }
        b.swap(next);
    }
    return loss;
}
// Fraction-free signed Schur complements. The stored array represents a positive
// scalar multiple of the actual form. A unimodular shear supplies a diagonal
// pivot if a nonzero trailing form has zero diagonal. Large entries go to GMP.
int small_deficit(const Matrix &input, int n, int cap) {
    using I = std::int64_t;
    using Wide = __int128_t;
    std::array<std::array<I, limit>, limit> a{};
    for (int i = 0; i < n; ++i)
        for (int j = 0; j < n; ++j)
            a[i][j] = input[i][j];
    I previous = 1;
    int loss = 0;
    for (int k = 0; k < n; ++k) {
        int u = -1;
        for (int i = k; i < n; ++i) {
            if (a[i][i] < 0) {
                u = i;
                break;
            }
            if (!a[i][i] && loss + 2 > cap) {
                for (int j = k; j < n; ++j)
                    if (a[i][j])
                        return loss + 2;
            }
            if (a[i][i] > 0 && (u < 0 || a[i][i] < a[u][u]))
                u = i;
        }
        if (u < 0) {
            int v = -1;
            for (int i = k; i < n && u < 0; ++i)
                for (int j = i + 1; j < n; ++j)
                    if (a[i][j]) {
                        u = i;
                        v = j;
                        break;
                    }
            if (u < 0)
                return loss + (n - k);
            for (int i = k; i < n; ++i)
                if (i != u) {
                    a[u][i] += a[v][i];
                    a[i][u] = a[u][i];
                }
            a[u][u] = 2 * a[u][v];
        }
        if (u != k) {
            std::swap(a[k], a[u]);
            for (int i = k; i < n; ++i)
                std::swap(a[i][k], a[i][u]);
        }
        const I p = a[k][k];
        assert(p);
        const I positive = p < 0 ? -p : p;
        if (p < 0)
            loss += 2;
        if (loss > cap)
            return loss;
        for (int i = k + 1; i < n; ++i)
            for (int j = i; j < n; ++j) {
                if (!a[i][k] || !a[k][j]) {
                    if (!a[i][j] || positive == previous)
                        continue;
                }
                const I direction = p < 0 ? -1 : 1;
                Wide numerator = Wide(positive) * a[i][j] - direction * Wide(a[i][k]) * a[k][j];
                Wide value;
                if (previous == 1)
                    value = numerator;
                else if (numerator >= INT64_MIN && numerator <= INT64_MAX) {
                    I short_value = I(numerator);
                    assert(short_value % previous == 0);
                    value = short_value / previous;
                } else {
                    assert(numerator % previous == 0);
                    value = numerator / previous;
                }
                if (value < -(Wide(1) << 55) || value > (Wide(1) << 55))
                    return exact_deficit(input, n);
                a[i][j] = a[j][i] = I(value);
            }
        previous = positive;
    }
    return loss;
}
struct Link {
    int i, j, lo, hi;
};
long long audit_stride = 0, audited = 0;
void signings(Matrix &a, int n, const std::vector<Link> &links, int index, int used) {
    if (found)
        return;
    if (index < int(links.size())) {
        auto [i, j, l, h] = links[index];
        for (int v = l; v <= h; v += 2) {
            a[i][j] = a[j][i] = v;
            signings(a, n, links, index + 1, used);
        }
        return;
    }
    if (strict)
        ++strict_forms[used];
    else
        ++forms[used];
    int cap = budget - used;
    bool audit = audit_stride && (((strict ? strict_forms : forms)[used] - 1) % audit_stride == 0);
    int loss = small_deficit(a, n, audit ? 2 * n : cap);
    if (audit) {
        assert(loss == characteristic_deficit(a, n));
        ++audited;
    }
    if (loss <= cap) {
        found = true;
        if (strict) {
            ++violations[used];
            std::cerr << "Strict surviving form at operation count " << used << " and deficit "
                      << loss << "\n";
            for (int i = 0; i < n; ++i) {
                for (int j = 0; j < n; ++j)
                    std::cerr << a[i][j] << ' ';
                std::cerr << '\n';
            }
        }
    }
}
void evaluate(const Graph &g, int used) {
    Matrix a{};
    std::vector<Link> links;
    std::array<int, limit> tree{};
    std::iota(tree.begin(), tree.end(), 0);
    for (int i = 0; i < g.n; ++i) {
        a[i][i] = g.weight[i] + 2 * g.a[i][i];
        for (int j = i + 1; j < g.n; ++j) {
            int m = g.a[i][j];
            if (!m)
                continue;
            int lo = -m, t = tree[i], u = tree[j];
            if (t != u) {
                lo = m % 2;
                for (int z = 0; z < g.n; ++z)
                    if (tree[z] == u)
                        tree[z] = t;
            }
            links.push_back({i, j, lo, m});
        }
    }
    signings(a, g.n, links, 0, used);
}
struct State {
    std::array<int, limit> id;
    std::uint64_t collapsed = 0;
};
void recurse(const Graph &c, const State &state, int next, int used) {
    if (found)
        return;
    std::array<int, limit> compact{};
    compact.fill(-1);
    Graph g;
    g.weight.fill(0);
    for (int i = 0; i < c.n; ++i)
        if (state.id[i] >= 0) {
            int &t = compact[state.id[i]];
            if (t < 0)
                t = g.n++;
            ++g.weight[t];
        }
    for (int k = 0; k < int(c.edges.size()); ++k)
        if (!(state.collapsed & (std::uint64_t(1) << k))) {
            auto [u, v] = c.edges[k];
            if (state.id[u] >= 0 && state.id[v] >= 0)
                g.add(compact[state.id[u]], compact[state.id[v]]);
        }
    assert(g.n == J - used);
    if (g.has_forest_matching(budget + 1 - used))
        return;
    ++domains[used];
    evaluate(g, used);
    if (used == budget)
        return;
    for (int ev = next; ev < J + int(c.edges.size()); ++ev) {
        State child = state;
        if (ev < J) {
            child.id[ev] = -1;
        } else {
            int i = ev - J;
            auto [u, v] = c.edges[i];
            int a = state.id[u], b = state.id[v];
            if (a < 0 || b < 0 || a == b)
                continue;
            if (i > 0 && c.edges[i] == c.edges[i - 1])
                continue; // parallel choices are interchangeable
            child.collapsed |= (std::uint64_t(1) << i);
            for (int k = 0; k < J; ++k)
                if (child.id[k] == b)
                    child.id[k] = a;
        }
        recurse(c, child, ev + 1, used + 1);
    }
}
void emit(const Graph &c) {
    std::string s(1 + (J * (J - 1) / 2 + 5) / 6, 63);
    s[0] = 63 + J;
    int k = 0;
    for (int j = 1; j < J; ++j)
        for (int i = 0; i < j; ++i, ++k)
            if (c.a[i][j])
                s[1 + k / 6] += char(32 >> (k % 6));
    std::cout << s << '\n';
}
// A second, tighter pass keeps each paid charge/deletion explicit.  At an
// intermediate quotient, independent equations either merge two distinct
// coordinates or kill a coordinate by a negative equation on an unused loop.
std::array<std::set<std::string>, 8> memo;
void strict_search(const Graph &g, int used) {
    if (found || g.has_forest_matching(budget + 1 - used))
        return;
    if (!memo[used].insert(g.key()).second)
        return;
    ++strict_domains[used];
    evaluate(g, used);
    if (used == budget || found)
        return;
    for (int u = 0; u < g.n; ++u) {
        Graph more = g;
        more.weight[u] += 2;
        strict_search(more, used + 1);
    }
    for (int u = 0; u < g.n; ++u)
        for (int v = u; v < g.n; ++v)
            if (g.a[u][v]) {
                auto id = [&](int x) { return x == v ? (u == v ? -1 : u) : x - (x > v); };
                Graph merged(g.n - 1);
                merged.weight.fill(0);
                for (int z = 0; z < g.n; ++z)
                    if (id(z) >= 0)
                        merged.weight[id(z)] += g.weight[z];
                Graph cut(g.n);
                cut.weight = g.weight;
                bool first = true;
                for (auto [i, j] : g.edges) {
                    if (i == u && j == v && first) {
                        first = false;
                        continue;
                    }
                    cut.add(i, j);
                    if (id(i) >= 0 && id(j) >= 0)
                        merged.add(id(i), id(j));
                }
                assert(!first);
                strict_search(merged, used + 1);
                if (u != v)
                    strict_search(cut, used + 1);
                if (found) {
                    std::cerr << " quotient edge " << u << "," << v << " at step " << used << "\n";
                    return;
                }
            }
}
void inspect(Graph &c) {
    ++cubic_count;
    std::sort(c.edges.begin(), c.edges.end());
    if (emit_only) {
        if (!c.has_forest_matching(budget + 1))
            emit(c);
        return;
    }
    State state{};
    std::iota(state.id.begin(), state.id.end(), 0);
    found = false;
    recurse(c, state, 0, 0);
    if (found) {
        ++exceptions;
        strict = true;
        found = false;
        for (auto &mem : memo)
            mem.clear();
        strict_search(c, 0);
        strict = false;
        if (found) {
            std::cerr << "strict witness cubic skeleton: ";
            for (auto [u, v] : c.edges)
                std::cerr << u << "," << v << " ";
            std::cerr << "\n";
            std::exit(2);
        }
    }
}
void inflate(const Graph &s, Bits blocks) {
    const int n = s.n;
    for (int i = 0; i < n; ++i)
        for (int j = i + 1; j < n; ++j)
            if (s.a[i][j] > 1 && !(blocks & (bit(i) | bit(j))))
                return;
    Graph c(n);
    std::array<int, limit> second{}, slots{};
    second.fill(-1);
    for (int i = 0; i < n; ++i)
        if (blocks & bit(i)) {
            second[i] = c.n++;
            c.add(i, second[i]);
            c.add(i, second[i]);
        }
    auto slot = [&](int i) {
        int pos = slots[i]++;
        if (second[i] < 0)
            return i;
        assert(pos <= 1);
        return pos ? second[i] : i;
    };
    for (auto [i, j] : s.edges) {
        int u = slot(i), v = slot(j);
        c.add(u, v);
    }
    for (int i = 0; i < n; ++i)
        while (slots[i] < (second[i] < 0 ? 3 : 2)) {
            int u = slot(i), v = c.n++;
            c.add(u, v);
            c.add(v, v);
        }
    assert(c.n == J);
    for (int i = 0; i < J; ++i)
        assert(c.degree[i] == 3);
    inspect(c);
}
void multiplicities(const Graph &simple, const Graph &s, int k) {
    if (k == int(simple.edges.size())) {
        int ell = int(s.edges.size()) - s.n + 1;
        if (2 * (s.n + 1 - ell) != J)
            return;
        Bits allowed = 0;
        for (int i = 0; i < s.n; ++i)
            if (s.degree[i] <= 2)
                allowed |= bit(i);
        for (Bits blocks = allowed;; blocks = (blocks - 1) & allowed) {
            inflate(s, blocks);
            if (!blocks)
                break;
        }
        return;
    }
    auto [u, v] = simple.edges[k];
    multiplicities(simple, s, k + 1);
    Graph copy = s;
    while (copy.degree[u] < 3 && copy.degree[v] < 3) {
        copy.add(u, v);
        multiplicities(simple, copy, k + 1);
    }
}
bool augment = false;
void complete(const std::string &s) { // independent: a cubic skeleton of order J
    Graph c = read(s);
    assert(c.n == J - (augment ? 2 : 0));
    Bits twos = 0;
    for (int i = 0; i < c.n; ++i) {
        if (c.degree[i] == 1)
            c.add(i, i);
        else if (c.degree[i] == 2)
            twos |= bit(i);
    }
    while (twos) {
        int v = -1;
        for (int i = 0; i < c.n; ++i)
            if ((twos & bit(i)) && __builtin_popcount(c.neighbors[i] & twos) <= 1) {
                v = i;
                break;
            }
        if (v < 0)
            v = __builtin_ctz(twos);
        Bits neighbors = c.neighbors[v] & twos;
        if (!neighbors)
            return;
        int u = __builtin_ctz(neighbors);
        c.add(u, v);
        twos &= ~(bit(u) | bit(v));
    }
    for (int i = 0; i < c.n; ++i)
        assert(c.degree[i] == 3);
    if (!augment) {
        inspect(c);
        return;
    }
    std::sort(c.edges.begin(), c.edges.end());
    const int x = c.n, y = x + 1;
    for (int e = 0; e < int(c.edges.size()); ++e) {
        if (e && c.edges[e - 1] == c.edges[e])
            continue;
        auto [u, v] = c.edges[e];
        Graph base(J);
        for (int t = 0; t < int(c.edges.size()); ++t)
            if (t != e)
                base.add(c.edges[t].first, c.edges[t].second);
        Graph loop = base;
        loop.add(u, x);
        loop.add(x, v);
        loop.add(x, y);
        loop.add(y, y);
        inspect(loop);
        base.add(u, x);
        base.add(x, y);
        base.add(x, y);
        base.add(y, v);
        inspect(base);
    }
}
} // namespace
int main(int argc, char **argv) {
    if (argc < 2) {
        std::cerr << "usage: forest_verify J [--budget=d] [--direct|--augment] [--emit] "
                     "[--audit=stride] < graphs.g6\n";
        return 1;
    }
    J = std::stoi(argv[1]);
    assert(J >= 4 && J <= 30 && J % 2 == 0);
    bool direct = false;
    for (int i = 2; i < argc; ++i) {
        std::string opt = argv[i];
        if (opt == "--direct")
            direct = true;
        else if (opt == "--augment") {
            direct = true;
            augment = true;
            emit_only = true;
        } else if (opt.rfind("--budget=", 0) == 0) {
            budget = std::stoi(opt.substr(9));
            assert(budget >= 1 && budget <= 5);
        } else if (opt == "--emit")
            emit_only = true;
        else if (opt.rfind("--audit=", 0) == 0) {
            audit_stride = std::stoll(opt.substr(8));
            assert(audit_stride >= 1);
        } else
            return 1;
    }
    std::string line;
    while (std::getline(std::cin, line)) {
        ++input_count;
        if (direct)
            complete(line);
        else {
            Graph g = read(line);
            if (g.n < J / 2 - 1)
                continue;
            assert(g.n <= 4 * budget);
            if (g.has_forest_matching(budget + 1))
                continue;
            multiplicities(g, g, 0);
        }
    }
    if (emit_only)
        return 0;
    std::cout << "c=" << J / 2 + 1 << " inputs=" << input_count << " cubic inflations=" << cubic_count
              << "\n";
    for (int q = 0; q <= budget; ++q)
        std::cout << "  rank loss " << q << "; retained partitions " << domains[q]
                  << "; signed forms " << forms[q] << "; violations " << violations[q] << "\n";
    std::cout << "Cubic inflations requiring tighter pass " << exceptions << ".\n";
    for (int q = 0; q <= budget; ++q)
        std::cout << "  tight rank/cost " << q << "; retained domains " << strict_domains[q]
                  << "; signed forms " << strict_forms[q] << "\n";
    std::cout << "Independent characteristic-polynomial checks " << audited << ".\n";
    return 0;
}
