// Return the union of prefix vertices that can support an infinite walk of
// successive overlapping ratio enclosures in one specified residue and one
// Gray coordinate system. The outer loops test all residues and both systems.
// phase_paths.py performs exact big-integer arithmetic and rank-compresses the
// endpoints, so only order comparisons and Boolean reachability are needed here.
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <functional>
#include <stdexcept>
#include <vector>

using Word = std::uint64_t;
using Masks = std::vector<Word>;
constexpr int period = 140;
constexpr int word_bits = 64;

struct Vertex {
    std::int32_t phase, first, second;
    std::int32_t lower[2], upper[2];
};
static_assert(sizeof(Vertex) == 7 * sizeof(std::int32_t));

void include(Word* target, const Word* source, int count) {
    for (int i = 0; i < count; ++i) target[i] |= source[i];
}

bool meet(const Word* first, const Word* second, int count) {
    for (int i = 0; i < count; ++i) if (first[i] & second[i]) return true;
    return false;
}

void insert(Word* mask, int j) {
    mask[j / word_bits] |= Word(1) << (j % word_bits);
}

bool contains(const Word* mask, int j) {
    return (mask[j / word_bits] >> (j % word_bits)) & 1;
}

// Tarjan component numbers of the phase-return graph.
std::vector<int> components(const std::vector<std::vector<int>>& edges) {
    const int n = static_cast<int>(edges.size());
    std::vector<int> index(n, -1), low(n), component(n, -1), stack;
    int clock = 0, count = 0;
    std::function<void(int)> visit = [&](int u) {
        index[u] = low[u] = clock++;
        stack.push_back(u);
        for (int v : edges[u]) {
            if (index[v] < 0) {
                visit(v);
                low[u] = std::min(low[u], low[v]);
            } else if (component[v] < 0) {
                low[u] = std::min(low[u], index[v]);
            }
        }
        if (low[u] == index[u]) {
            int v;
            do {
                v = stack.back();
                stack.pop_back();
                component[v] = count;
            } while (v != u);
            ++count;
        }
    };
    for (int u = 0; u < n; ++u) if (index[u] < 0) visit(u);
    return component;
}

std::vector<unsigned char> retain(const std::vector<Vertex>& vertices) {
    const auto n = vertices.size();
    std::vector<std::vector<int>> layers(period);
    std::vector<int> position(n);
    std::vector<unsigned char> keep(n, 0);
    std::size_t largest = 0;
    for (std::size_t k = 0; k < n; ++k) {
        auto& layer = layers[vertices[k].phase];
        position[k] = static_cast<int>(layer.size());
        layer.push_back(static_cast<int>(k));
        largest = std::max(largest, layer.size());
    }

    for (int residue = 0; residue < period; ++residue) {
        const auto& anchor = layers[residue];
        if (anchor.empty()) continue;
        const int m = static_cast<int>(anchor.size());
        const int width = (m + word_bits - 1) / word_bits;
        auto offset = [width](int i) { return std::size_t(i) * width; };
        Masks current(largest * width), next(current.size());
        Masks forward(n * width), admissible(std::size_t(m) * width);
        for (int i = 0; i < m; ++i) insert(&current[offset(i)], i);

        // Preserve the source labels reaching each intermediate vertex.
        for (int d = 0; d < period; ++d) {
            const auto& layer = layers[(residue + d) % period];
            const auto& target = layers[(residue + d + 1) % period];
            std::fill_n(next.begin(), target.size() * width, 0);
            for (int k : layer) {
                const Word* source = &current[offset(position[k])];
                std::copy_n(source, width, &forward[offset(k)]);
                for (int v : {vertices[k].first, vertices[k].second})
                    if (v >= 0) include(&next[offset(position[v])], source, width);
            }
            current.swap(next);
        }

        // For each observable build the near-return graph, allowing only pairs
        // with intersecting closed ratio intervals and a real graph path.
        for (int coordinate = 0; coordinate < 2; ++coordinate) {
            auto sorted = anchor;
            std::sort(sorted.begin(), sorted.end(), [&](int u, int v) {
                return vertices[u].lower[coordinate] < vertices[v].lower[coordinate];
            });
            std::vector<std::vector<int>> edges(m);
            auto add_if_reachable = [&](int u, int v) {
                int i = position[u], j = position[v];
                if (contains(&current[offset(j)], i)) edges[i].push_back(j);
            };
            std::vector<int> active;
            for (int v : sorted) {
                active.erase(std::remove_if(active.begin(), active.end(), [&](int u) {
                    return vertices[u].upper[coordinate] < vertices[v].lower[coordinate];
                }), active.end());
                add_if_reachable(v, v);
                for (int u : active) {
                    add_if_reachable(u, v);
                    add_if_reachable(v, u);
                }
                active.push_back(v);
            }
            const auto label = components(edges);
            for (int i = 0; i < m; ++i) for (int j : edges[i])
                if (label[i] == label[j]) {
                    insert(&admissible[offset(j)], i);
                    keep[anchor[i]] = keep[anchor[j]] = 1;
                }
        }

        // Intersect forward source labels with the backwards requirement for
        // admissible endpoints. The two endpoint copies are separate layers.
        std::copy(admissible.begin(), admissible.end(), current.begin());
        for (int d = period - 1; d > 0; --d) {
            const auto& layer = layers[(residue + d) % period];
            std::fill_n(next.begin(), layer.size() * width, 0);
            for (int k : layer) {
                Word* mask = &next[offset(position[k])];
                for (int v : {vertices[k].first, vertices[k].second})
                    if (v >= 0) include(mask, &current[offset(position[v])], width);
                if (!keep[k] && meet(&forward[offset(k)], mask, width)) keep[k] = 1;
            }
            current.swap(next);
        }
    }
    return keep;
}

int main() {
    std::int32_t n;
    if (std::fread(&n, sizeof(n), 1, stdin) != 1 || n <= 0) return 1;
    std::vector<Vertex> vertices(n);
    if (std::fread(vertices.data(), sizeof(Vertex), n, stdin) != std::size_t(n)) return 1;
    for (const auto& vertex : vertices) {
        if (!(0 <= vertex.phase && vertex.phase < period)) return 1;
        for (int k : {vertex.first, vertex.second})
            if (k < -1 || k >= n || (k >= 0 && vertices[k].phase != (vertex.phase+1)%period))
                return 1;
    }
    const auto keep = retain(vertices);
    return std::fwrite(keep.data(), 1, keep.size(), stdout) == keep.size() ? 0 : 1;
}
