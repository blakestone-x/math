// Finite certificate for the line-graph signature deficit-three bound.
// Build with a C++17 compiler and GNU GMP, as described in the accompanying note.
#ifdef NDEBUG
#error The finite certificate requires assertions.
#endif
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <gmpxx.h>
#include <iostream>
#include <map>
#include <numeric>
#include <set>
#include <string>
#include <utility>
#include <vector>

using namespace std;
using cpp_int = mpz_class;
using Edge = pair<int, int>;
const int capacity = 29;
using Matrix = array<array<int, capacity>, capacity>;
struct Kernel {
    int n = 0;
    vector<Edge> e;
    Matrix a{};
    array<int, capacity> degree{}, neighbors{};
    void add(int u, int v) {
        if (u > v)
            swap(u, v);
        e.emplace_back(u, v);
        a[u][v]++;
        if (u != v) {
            a[v][u]++;
            neighbors[u] |= 1 << v;
            neighbors[v] |= 1 << u;
        }
        degree[u]++;
        degree[v]++;
    }
    vector<Edge> qualifying() const {
        vector<Edge> ans;
        for (int u = 0; u < n; u++)
            for (int v = u + 1; v < n; v++)
                if (degree[u] == 3 && degree[v] == 3 && !a[u][u] && !a[v][v] && a[u][v] == 1)
                    ans.emplace_back(u, v);
        return ans;
    }
    int packing(const vector<Edge> &good, int cap) const {
        int best = 0;
        for (int i = 0; i < (int)good.size(); i++) {
            auto [u, v] = good[i];
            int blocked = (1 << u) | (1 << v) | neighbors[u] | neighbors[v];
            best = max(best, 1);
            if (best >= cap)
                return best;
            for (int j = i + 1; j < (int)good.size(); j++) {
                auto [x, y] = good[j];
                if (blocked & ((1 << x) | (1 << y)))
                    continue;
                best = 2;
                if (best >= cap)
                    return best;
                int next = blocked | (1 << x) | (1 << y) | neighbors[x] | neighbors[y];
                for (int k = j + 1; k < (int)good.size(); k++)
                    if (!(next & ((1 << good[k].first) | (1 << good[k].second))))
                        return 3;
            }
        }
        return best;
    }
    Kernel contract(int index) const {
        auto [u, v] = e[index];
        assert(u < v);
        auto id = [&](int i) { return i == v ? u : i - (i > v); };
        Kernel h;
        h.n = n - 1;
        for (int j = 0; j < (int)e.size(); j++)
            if (j != index)
                h.add(id(e[j].first), id(e[j].second));
        sort(h.e.begin(), h.e.end());
        return h;
    }
    string key() const {
        string s;
        for (int i = 0; i < n; i++)
            for (int j = i; j < n; j++)
                s += (char)a[i][j];
        return s;
    }
};

struct Relations {
    vector<int> root, sign;
    vector<bool> killed;
    explicit Relations(int n) : root(n), sign(n, 1), killed(n, false) {
        iota(root.begin(), root.end(), 0);
    }
    // Relations preserve the explicit coordinate description x_i = sign[i]*x_root.
    void impose(int u, int v, int s) {
        int a = root[u], b = root[v], t = s * sign[u] * sign[v];
        if (a == b) {
            if (t == -1)
                killed[a] = true;
            return;
        }
        killed[a] = killed[a] || killed[b];
        for (int i = 0; i < (int)root.size(); i++)
            if (root[i] == b) {
                root[i] = a;
                sign[i] *= t;
            }
    }
};

struct Counts {
    long long kernels = 0, patterns = 0, forms = 0, exact = 0, violations = 0;
};
int J;
Counts tally[3][3];
set<string> used[3];
long long topologies[4];
bool check_all = false;
bool compressed = false;
bool emit_kernels = false;

int changes(const vector<int> &seq) {
    int last = 0, total = 0;
    for (int s : seq)
        if (s) {
            if (last && last != s)
                total++;
            last = s;
        }
    return total;
}

// Faddeev--LeVerrier and Descartes' rule on a real-rooted polynomial and its reflection.
// Multiprecision integer operations are exact, also at singular matrices.
int signature(const Matrix &a, int n) {
    using BigMatrix = array<array<cpp_int, capacity>, capacity>;
    BigMatrix b{}, next{};
    for (int i = 0; i < n; i++)
        b[i][i] = 1;
    vector<int> p = {1}, q = {1};
    for (int k = 1; k <= n; k++) {
        for (int i = 0; i < n; i++)
            for (int j = 0; j < n; j++)
                next[i][j] = 0;
        for (int i = 0; i < n; i++)
            for (int t = 0; t < n; t++)
                if (a[i][t])
                    for (int j = 0; j < n; j++)
                        next[i][j] += a[i][t] * b[t][j];
        cpp_int tr = 0;
        for (int i = 0; i < n; i++)
            tr += next[i][i];
        assert(tr % k == 0);
        cpp_int coef = -tr / k;
        int s = (coef > 0) - (coef < 0);
        p.push_back(s);
        q.push_back((k & 1) ? -s : s);
        for (int i = 0; i < n; i++)
            next[i][i] += coef;
        swap(b, next);
    }
    return changes(p) - changes(q);
}

// Exact symmetric congruence using 1x1 nonzero diagonals or a hyperbolic 2x2
// pivot. Common positive content is divided out after every Schur complement.
int congruence(const Matrix &a, int n) {
    vector<vector<cpp_int>> b(n, vector<cpp_int>(n));
    for (int i = 0; i < n; i++)
        for (int j = 0; j < n; j++)
            b[i][j] = a[i][j];
    int ans = 0;
    while (!b.empty()) {
        n = b.size();
        int u = 0;
        while (u < n && b[u][u] == 0)
            u++;
        int v = -1;
        if (u == n) {
            for (int i = 0; i < n && v == -1; i++)
                for (int j = i + 1; j < n; j++)
                    if (b[i][j] != 0) {
                        u = i;
                        v = j;
                        break;
                    }
            if (v == -1)
                break;
        }
        cpp_int pivot = v == -1 ? b[u][u] : b[u][v];
        int sgn = pivot > 0 ? 1 : -1;
        if (v == -1)
            ans += sgn;
        if (sgn < 0)
            pivot = -pivot;
        vector<int> keep;
        for (int i = 0; i < n; i++)
            if (i != u && i != v)
                keep.push_back(i);
        int m = keep.size();
        vector<vector<cpp_int>> next(m, vector<cpp_int>(m));
        cpp_int content = 0;
        for (int i = 0; i < m; i++)
            for (int j = i; j < m; j++) {
                int x = keep[i], y = keep[j];
                cpp_int correction;
                if (v == -1)
                    correction = b[x][u] * b[u][y];
                else
                    correction = b[x][u] * b[v][y] + b[x][v] * b[u][y];
                next[i][j] = pivot * b[x][y] - sgn * correction;
                mpz_gcd(content.get_mpz_t(), content.get_mpz_t(), next[i][j].get_mpz_t());
            }
        if (content == 0)
            break;
        for (int i = 0; i < m; i++)
            for (int j = i; j < m; j++) {
                next[i][j] /= content;
                if (i != j)
                    next[j][i] = next[i][j];
            }
        b.swap(next);
    }
    return ans;
}

// If deficit is zero the matrix must be positive definite. A deficit of one
// allows positive semidefinite matrices of nullity at most one.
bool fails_principal_tests(const Matrix &a, int n, int deficit) {
    if (deficit > 1)
        return false;
    int singular_pair_count = 0, previous_u = -1, previous_v = -1;
    for (int u = 0; u < n; u++) {
        if (a[u][u] < 0 || (!deficit && !a[u][u]))
            return true;
        for (int v = u + 1; v < n; v++) {
            int d = a[u][u] * a[v][v] - a[u][v] * a[u][v];
            if (d < 0 || (!deficit && !d))
                return true;
            if (!d && a[u][u] > 0 && a[v][v] > 0) {
                if (u != previous_u || v != previous_v)
                    singular_pair_count++;
                previous_u = u;
                previous_v = v;
                if (singular_pair_count >= 2)
                    return true;
            }
        }
    }
    return false;
}
void signs(Matrix &a, int n, const vector<Edge> &edges, const vector<vector<int>> &weights,
           int index, int deficit, Counts &counts) {
    if (index == (int)edges.size()) {
        counts.forms++;
        if (!check_all && fails_principal_tests(a, n, deficit))
            return;
        counts.exact++;
        int value = signature(a, n);
        if (check_all)
            assert(congruence(a, n) == value);
        if (n - value <= deficit)
            counts.violations++;
        return;
    }
    auto [i, j] = edges[index];
    for (int s : weights[index]) {
        a[i][j] = a[j][i] = s;
        signs(a, n, edges, weights, index + 1, deficit, counts);
    }
    a[i][j] = a[j][i] = 0;
}

enum class Kind { leaf, cut, even };
struct Event {
    Kind type;
    int edge, parity, affected;
};
void test(const Kernel &g, const vector<Edge> &good, int packing, const vector<Event> &ev) {
    int s = J - g.n, q = ev.size(), deficit = 2 - s - q;
    int mask = 0;
    for (auto &event : ev)
        mask |= event.affected;
    int untouched = 0;
    for (auto [u, v] : good)
        if (!(mask & ((1 << u) | (1 << v))))
            untouched++;
    if ((deficit == 0 && untouched) || (deficit == 1 && untouched >= 2) ||
        (deficit == 2 && packing >= 2 && untouched >= 3))
        return;
    auto &counts = tally[s][q];
    vector<int> diag(g.n);
    for (int i = 0; i < g.n; i++)
        diag[i] = g.degree[i] - 2;
    vector<bool> omitted(g.e.size());
    Relations eq(g.n);
    int rank = 0;
    for (auto event : ev) {
        if (event.type == Kind::leaf) {
            diag[event.edge] += 2;
            continue;
        }
        if (omitted[event.edge])
            return;
        omitted[event.edge] = true;
        if (event.type == Kind::even) {
            auto [u, v] = g.e[event.edge];
            eq.impose(u, v, event.parity);
            rank++;
        }
    }
    vector<int> id(g.n, -1);
    int n = 0;
    for (int i = 0; i < g.n; i++)
        if (eq.root[i] == i && !eq.killed[i])
            id[i] = n++;
    if (n != g.n - rank)
        return; // dependent selections were represented by a smaller basis
    vector<int> coord(g.n);
    Matrix base{}, mult{};
    for (int i = 0; i < g.n; i++) {
        coord[i] = id[eq.root[i]];
        if (coord[i] >= 0)
            base[coord[i]][coord[i]] += diag[i];
    }
    for (int k = 0; k < (int)g.e.size(); k++)
        if (!omitted[k]) {
            auto [i, j] = g.e[k];
            int a = coord[i], b = coord[j];
            if (a < 0 || b < 0)
                continue;
            if (a == b)
                base[a][a] += 2; // positive odd loops dominate negative odd loops
            else {
                mult[a][b]++;
                mult[b][a]++;
            }
        }
    counts.patterns++;
    vector<Edge> pairs;
    vector<vector<int>> weights;
    vector<int> root(n);
    iota(root.begin(), root.end(), 0);
    for (int i = 0; i < n; i++)
        for (int j = i + 1; j < n; j++)
            if (mult[i][j]) {
                int ri = root[i], rj = root[j], m = mult[i][j], lo = -m;
                if (ri != rj) {
                    for (int &r : root)
                        if (r == rj)
                            r = ri;
                    lo = m % 2; // forest weight can be switched to be nonnegative
                }
                pairs.emplace_back(i, j);
                weights.emplace_back();
                for (int w = lo; w <= m; w += 2)
                    weights.back().push_back(w);
            }
    long long before = counts.violations;
    signs(base, n, pairs, weights, 0, deficit, counts);
    if (before != counts.violations) {
        cerr << "relaxation witness J=" << J << " b=" << g.n << " q=" << q << " edges: ";
        for (auto [a, b] : g.e)
            cerr << a << "," << b << " ";
        cerr << " events:";
        for (auto e : ev)
            cerr << " " << (int)e.type << "," << e.edge << "," << e.parity;
        cerr << "\n";
        exit(2);
    }
}
void inspect(const Kernel &g) {
    int s = J - g.n;
    if (s && !used[s].insert(g.key()).second)
        return;
    auto good = g.qualifying();
    int pack = g.packing(good, 3 - s);
    if (pack >= 3 - s)
        return;
    tally[s][0].kernels++;
    test(g, good, pack, {});
    if (s < 2) {
        vector<Event> ev;
        for (int v = 0; v < g.n; v++)
            ev.push_back({Kind::leaf, v, 1, 1 << v});
        for (int j = 0; j < (int)g.e.size(); j++) {
            auto [u, v] = g.e[j];
            int mask = (1 << u) | (1 << v);
            ev.push_back({Kind::cut, j, 1, mask});
            if (u != v)
                ev.push_back({Kind::even, j, 1, mask});
            ev.push_back({Kind::even, j, -1, mask});
        }
        for (int i = 0; i < (int)ev.size(); i++) {
            test(g, good, pack, {ev[i]});
            if (s == 0)
                for (int j = i; j < (int)ev.size(); j++)
                    test(g, good, pack, {ev[i], ev[j]});
        }
        Edge previous = {-1, -1};
        for (int i = 0; i < (int)g.e.size(); i++) {
            Edge current = g.e[i];
            if (current != previous && current.first != current.second)
                inspect(g.contract(i));
            previous = current;
        }
    }
}

// A simple connected subcubic skeleton uniquely determines its (possible)
// cubic completion, up to the two isomorphic alternations on an even cycle.
Kernel read_graph(const string &s) {
    assert(!s.empty());
    int n = s[0] - 63;
    assert(n > 1 && n < capacity);
    assert(s.size() == 1 + (n * (n - 1) / 2 + 5) / 6);
    Kernel g;
    g.n = n;
    int k = 0;
    for (int y = 1; y < n; y++)
        for (int x = 0; x < y; x++, k++)
            if ((s[1 + k / 6] - 63) & (32 >> (k % 6)))
                g.add(x, y);
    return g;
}
void emit(const Kernel &g);
void complete(const string &s) {
    auto g = read_graph(s);
    int n = g.n;
    assert(n == J);
    int twos = 0;
    for (int i = 0; i < n; i++) {
        if (g.degree[i] == 1)
            g.add(i, i);
        else if (g.degree[i] == 2)
            twos |= 1 << i;
    }
    while (twos) {
        int v = -1;
        for (int i = 0; i < n; i++)
            if ((twos & (1 << i)) && __builtin_popcount(g.neighbors[i] & twos) <= 1) {
                v = i;
                break;
            }
        if (v < 0)
            v = __builtin_ctz(twos);
        int nb = g.neighbors[v] & twos;
        if (!nb)
            return;
        int u = __builtin_ctz(nb);
        g.add(u, v);
        twos &= ~((1 << u) | (1 << v));
    }
    for (int i = 0; i < n; i++)
        assert(g.degree[i] == 3);
    sort(g.e.begin(), g.e.end());
    int pack = g.packing(g.qualifying(), 3);
    topologies[pack]++;
    if (pack < 3) {
        if (emit_kernels)
            emit(g);
        else
            inspect(g);
    }
}
void emit(const Kernel &g) {
    string s(1 + (g.n * (g.n - 1) / 2 + 5) / 6, 63);
    s[0] = 63 + g.n;
    int k = 0;
    for (int y = 1; y < g.n; y++)
        for (int x = 0; x < y; x++, k++)
            if (g.a[x][y])
                s[1 + k / 6] += (32 >> (k % 6));
    cout << s << "\n";
}

// Inflate ordinary cubic vertices and paired endpoints of a double edge.
// Each free outside slot receives a separate vertex with one loop.
void inflate(const Kernel &h, int blocks) {
    const int n = h.n;
    for (int i = 0; i < n; i++)
        for (int j = i + 1; j < n; j++)
            if (h.a[i][j] > 1 && !(blocks & ((1 << i) | (1 << j))))
                return;
    Kernel g;
    g.n = n;
    vector<int> second(n, -1), used_slots(n, 0);
    for (int i = 0; i < n; i++)
        if (blocks & (1 << i)) {
            second[i] = g.n++;
            g.add(i, second[i]);
            g.add(i, second[i]);
        }
    auto slot = [&](int i) {
        int idx = used_slots[i]++;
        if (second[i] < 0)
            return i;
        assert(idx <= 1);
        return idx == 0 ? i : second[i];
    };
    for (auto [i, j] : h.e) {
        int u = slot(i), v = slot(j);
        g.add(u, v);
    }
    for (int i = 0; i < n; i++)
        while (used_slots[i] < (second[i] < 0 ? 3 : 2)) {
            int u = slot(i), v = g.n++;
            g.add(u, v);
            g.add(v, v);
        }
    assert(g.n == J);
    sort(g.e.begin(), g.e.end());
    int pack = g.packing(g.qualifying(), 3);
    topologies[pack]++;
    if (pack < 3) {
        if (emit_kernels)
            emit(g);
        else
            inspect(g);
    }
}
void multiplicities(const Kernel &simple, const Kernel &h, int k) {
    if (k == (int)simple.e.size()) {
        int ell = h.e.size() - h.n + 1;
        if (2 * (h.n + 1 - ell) != J)
            return;
        int allowed = 0;
        for (int i = 0; i < h.n; i++)
            if (h.degree[i] <= 2)
                allowed |= 1 << i;
        int mask = allowed;
        while (true) {
            inflate(h, mask);
            if (!mask)
                break;
            mask = (mask - 1) & allowed;
        }
        return;
    }
    auto [i, j] = simple.e[k];
    multiplicities(simple, h, k + 1);
    Kernel more = h;
    while (more.degree[i] < 3 && more.degree[j] < 3) {
        more.add(i, j);
        multiplicities(simple, more, k + 1);
    }
}
void compressed_cubic(const string &s) {
    auto h = read_graph(s);
    if (h.n < J / 2 - 1)
        return;
    assert(h.n <= 12);
    if (h.packing(h.e, 3) >= 3)
        return;
    multiplicities(h, h, 0);
}
int main(int argc, char **argv) {
    if (argc < 2) {
        cerr << "usage: checker J [--compressed] [--all-inertias] [--emit-kernels] < geng.g6\n";
        return 1;
    }
    J = stoi(argv[1]);
    for (int i = 2; i < argc; i++) {
        string opt = argv[i];
        if (opt == "--compressed")
            compressed = true;
        else if (opt == "--all-inertias")
            check_all = true;
        else if (opt == "--emit-kernels")
            emit_kernels = true;
        else
            return 1;
    }
    assert(J >= 14 && J <= 26 && J % 2 == 0);
    if (!compressed)
        assert(J == 14 || J == 16);
    string line;
    long long simple = 0;
    while (getline(cin, line)) {
        if (compressed)
            compressed_cubic(line);
        else
            complete(line);
        simple++;
    }
    if (compressed)
        assert(simple == 27505);
    else
        assert(simple == (J == 14 ? 262044 : 4101318));
    if (emit_kernels)
        return 0;
    if (!compressed) {
        long long cubic = accumulate(topologies, topologies + 4, 0LL);
        assert(cubic == (J == 14 ? 21096 : 204638));
    }
    cout << "J=" << J << " simple skeletons " << simple << "; cubic by packing 0, 1, 2, 3+:";
    for (auto t : topologies)
        cout << " " << t;
    cout << "\n";
    for (int s = 0; s <= 2; s++) {
        cout << "contraction count " << s << "; retained labelled kernels " << tally[s][0].kernels
             << "\n";
        for (int q = 0; q <= 2 - s; q++) {
            const auto &x = tally[s][q];
            cout << "  charged operations " << q << "; patterns " << x.patterns << "; signed forms "
                 << x.forms << "; full characteristic polynomials " << x.exact << "; violations "
                 << x.violations << "\n";
        }
    }
}
