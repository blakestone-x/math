"""Exact finite proof for f(6) and f(7). Run beside the companion verify.py.

Python 3.9 or later. No third-party libraries. --cross-check also evaluates all
rank-one forms by an independent symmetric-congruence inertia computation.
"""

import argparse
from collections import Counter, defaultdict
from itertools import combinations, product

from verify import inertia


def ordered_edges(edges):
    return tuple(sorted(tuple(sorted(edge)) for edge in edges))


def adjacency(order, edges):
    result = [[0] * order for _ in range(order)]
    for i, j in edges:
        result[i][j] += 1
        if i != j:
            result[j][i] += 1
    return result


def canonical(order, edges):
    """Exact isomorphism code by equitable refinement and individualization."""
    matrix = adjacency(order, edges)
    cells = defaultdict(list)
    for i, row in enumerate(matrix):
        key = sum(row) + row[i], row[i]
        cells[key].append(i)

    def refine(partition):
        while True:
            refined = []
            for cell in partition:
                subcells = defaultdict(list)
                for v in cell:
                    key = tuple(tuple(sorted(matrix[v][w] for w in other)) for other in partition)
                    subcells[key].append(v)
                refined.extend(subcells[key] for key in sorted(subcells))
            if len(refined) == len(partition):
                return refined
            partition = refined

    def visit(partition):
        partition = refine(partition)
        if len(partition) == order:
            labels = [cell[0] for cell in partition]
            return bytes(matrix[v][w] for i, v in enumerate(labels) for w in labels[i:])
        _, index = min((len(cell), i) for i, cell in enumerate(partition) if len(cell) > 1)
        cell = partition[index]
        return min(
            visit(partition[:index] + [[v], [w for w in cell if w != v]] + partition[index+1:])
            for v in cell
        )

    return visit([cells[key] for key in sorted(cells)])


def expand_cubic(order, previous):
    """Insert a hanging loop, or subdivide two positions and connect them."""
    collected = {}
    for edges in previous:
        def accept(new_edges):
            new_edges = ordered_edges(new_edges)
            key = canonical(order + 2, new_edges)
            collected.setdefault(key, new_edges)

        for edge in set(edges):
            u, v = edge
            remaining = list(edges)
            remaining.remove(edge)
            accept(remaining + [(u, order), (v, order), (order, order+1), (order+1, order+1)])
            accept(remaining + [(u, order), (v, order+1), (order, order+1), (order, order+1)])
        for first, second in set(combinations(edges, 2)):
            remaining = list(edges)
            remaining.remove(first)
            remaining.remove(second)
            accept(remaining + [(v, order) for v in first] +
                   [(v, order+1) for v in second] + [(order, order+1)])
    return list(collected.values())


def contract(edges, u, v):
    def index(i):
        return u if i == v else i - (i > v)
    rest = list(edges)
    rest.remove((u, v))
    return ordered_edges((index(a), index(b)) for a, b in rest)


def packing_capped_at_two(order, edges):
    matrix = adjacency(order, edges)
    cubic_loopless = [i for i, row in enumerate(matrix) if row[i] == 0 and sum(row) == 3]
    good = [(u, v) for u, v in combinations(cubic_loopless, 2) if matrix[u][v] == 1]
    for (a, b), (c, d) in combinations(good, 2):
        if len({a, b, c, d}) == 4 and not any(
                matrix[u][v] for u in (a, b) for v in (c, d)):
            return 2
    return int(bool(good))


def exceptional_kernels(order, cubic):
    low = {}
    high = []
    for edges in cubic:
        if packing_capped_at_two(order, edges) < 2:
            high.append(edges)
        for u, v in set(edges):
            if u == v:
                continue
            compressed = contract(edges, u, v)
            if not packing_capped_at_two(order-1, compressed):
                low.setdefault(canonical(order-1, compressed), compressed)
    return list(low.values()), high


def switch_classes(order, edges):
    """Switch signs to + along a spanning forest, then vary every chord sign."""
    parent = list(range(order))

    def root(v):
        while v != parent[v]:
            v = parent[v]
        return v

    chords = []
    for i, (u, v) in enumerate(edges):
        a, b = root(u), root(v)
        if a == b:
            chords.append(i)
        else:
            parent[a] = b
    for signs in product((1, -1), repeat=len(chords)):
        all_signs = [1] * len(edges)
        for i, value in zip(chords, signs):
            all_signs[i] = value
        yield all_signs


def form(diagonal, edges, signs):
    matrix = [[0] * len(diagonal) for _ in diagonal]
    for i, value in enumerate(diagonal):
        matrix[i][i] = value
    for (i, j), sign in zip(edges, signs):
        matrix[i][j] += sign
        matrix[j][i] += sign
    return matrix


def positive_definite(matrix):
    """Unpivoted Bareiss elimination. All leading principal minors must be positive."""
    upper = [row[:] for row in matrix]
    previous = 1
    for k in range(len(upper)):
        pivot = upper[k][k]
        if pivot <= 0:
            return False
        for i in range(k+1, len(upper)):
            for j in range(i, len(upper)):
                numerator = pivot * upper[i][j] - upper[k][i] * upper[k][j]
                assert numerator % previous == 0
                upper[i][j] = numerator // previous
        previous = pivot
    return True


def rank_zero(order, exceptional, allow_leaf):
    worst = -10**6
    count = 0
    for edges in exceptional:
        diagonal = [-2] * order
        for u, v in edges:
            diagonal[u] += 1
            diagonal[v] += 1
        for signs in switch_classes(order, edges):
            base = form(diagonal, edges, signs)
            for leaf in [None] + (list(range(order)) if allow_leaf else []):
                if leaf is not None:
                    base[leaf][leaf] += 2
                pos, _, neg = inertia(base)
                worst = max(worst, pos-neg-int(leaf is not None))
                count += 1
                if leaf is not None:
                    base[leaf][leaf] -= 2
    return count, worst


def rank_one_restrictions(order, edges):
    """Yield diagonals and odd edges on ker(U^t), after fixing the even endpoint sign."""
    for index in [-1] + list(range(len(edges))):
        for extra in ([0] if index == -1 else [1, 2]):
            links = list(edges)
            diagonal = [1] * order + [2] * extra
            if extra:
                u, v = links.pop(index)
                path = [u] + list(range(order, order+extra)) + [v]
                links.extend(zip(path, path[1:]))
            links = list(ordered_edges(links))
            for pair, multiplicity in Counter(links).items():
                u, v = pair
                if any(i not in pair for i in range(order, order+extra)):
                    continue
                for even_count in range(1, multiplicity+1):
                    odd = links[:]
                    for _ in range(even_count):
                        odd.remove(pair)
                    if u == v:
                        # Constraint x_u = 0.
                        cut_diagonal = diagonal[:u] + diagonal[u+1:]
                        cut_edges = [(i-(i>u), j-(j>u)) for i, j in odd if u not in (i, j)]
                    else:
                        # Constraint x_v = x_u after a coordinate sign switch.
                        def index_after(i):
                            return u if i == v else i - (i > v)
                        cut_diagonal = diagonal[:v] + diagonal[v+1:]
                        cut_diagonal[u] += diagonal[v]
                        cut_edges = [(index_after(i), index_after(j)) for i, j in odd]
                    yield cut_diagonal, cut_edges


def rank_one(order, exceptional, cross_check):
    count = 0
    for edges in exceptional:
        for diagonal, odd in rank_one_restrictions(order, edges):
            for signs in switch_classes(len(diagonal), odd):
                matrix = form(diagonal, odd, signs)
                assert not positive_definite(matrix)
                if cross_check:
                    positive, _, _ = inertia(matrix)
                    assert positive < len(diagonal)
                count += 1
    return count


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cross-check", action="store_true")
    args = parser.parse_args()
    cubic = [ordered_edges([(0, 1)]*3), ordered_edges([(0, 0), (0, 1), (1, 1)])]
    expected_counts = {4: 5, 6: 17, 8: 71, 10: 388, 12: 2592}
    limits = {10: (9, 26, (576, 8), (18304, 8), 92416),
              12: (4, 13, (512, 9), (21632, 10), 110208)}
    for order, expected in expected_counts.items():
        cubic = expand_cubic(order-2, cubic)
        assert len(cubic) == expected
        print(f"connected cubic kernels on {order} vertices: {len(cubic)}", flush=True)
        if order not in limits:
            continue
        low, high = exceptional_kernels(order, cubic)
        low_count, high_count, low_expected, high_expected, one_expected = limits[order]
        assert (len(low), len(high)) == (low_count, high_count)
        lo = rank_zero(order-1, low, allow_leaf=False)
        hi = rank_zero(order, high, allow_leaf=True)
        single = rank_one(order, high, args.cross_check)
        assert (lo, hi, single) == (low_expected, high_expected, one_expected)
        print(f"exceptional kernel counts: b={order-1}: {len(low)}, b={order}: {len(high)}")
        print(f"rank-zero forms and maximum net signatures: {lo}, {hi}")
        print(f"rank-one forms excluded by exact Sylvester tests: {single}", flush=True)
    if args.cross_check:
        print("all rank-one exclusions also verified by integral congruence inertia")


if __name__ == "__main__":
    main()
