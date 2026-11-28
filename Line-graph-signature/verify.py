"""Independent finite checks for the line-graph signature manuscript. Python 3.9+."""

from fractions import Fraction
from functools import reduce
from itertools import combinations, combinations_with_replacement
from math import gcd
from random import Random


def inertia(matrix):
    """Exact congruence with 1x1 and 2x2 pivots, using positive integral scaling."""
    matrix = [row[:] for row in matrix]
    positive = negative = 0
    while matrix:
        n = len(matrix)
        i = next((i for i in range(n) if matrix[i][i]), None)
        if i is not None:
            pivot = matrix[i][i]
            sign = 1 if pivot > 0 else -1
            positive += sign > 0
            negative += sign < 0
            rest = [u for u in range(n) if u != i]
            matrix = [
                [abs(pivot) * matrix[u][v] - sign * matrix[u][i] * matrix[i][v]
                 for v in rest] for u in rest
            ]
        else:
            edge = next(((i, j) for i, j in combinations(range(n), 2) if matrix[i][j]), None)
            if edge is None:
                return positive, n, negative
            i, j = edge
            pivot = matrix[i][j]
            sign = 1 if pivot > 0 else -1
            positive += 1
            negative += 1
            rest = [u for u in range(n) if u not in (i, j)]
            matrix = [
                [abs(pivot) * matrix[u][v] -
                 sign * (matrix[u][i] * matrix[j][v] + matrix[u][j] * matrix[i][v])
                 for v in rest] for u in rest
            ]
        divisor = reduce(gcd, (abs(value) for row in matrix for value in row), 0)
        if divisor > 1:
            matrix = [[value // divisor for value in row] for row in matrix]
    return positive, 0, negative


def det(matrix):
    """Exact Bareiss elimination with row pivoting."""
    matrix = [row[:] for row in matrix]
    sign = divisor = 1
    if not matrix:
        return 1
    for j in range(len(matrix) - 1):
        i = next((i for i in range(j, len(matrix)) if matrix[i][j]), None)
        if i is None:
            return 0
        if i != j:
            matrix[j], matrix[i] = matrix[i], matrix[j]
            sign = -sign
        pivot = matrix[j][j]
        for i in range(j + 1, len(matrix)):
            for k in range(j + 1, len(matrix)):
                numerator = pivot * matrix[i][k] - matrix[i][j] * matrix[j][k]
                assert numerator % divisor == 0
                matrix[i][k] = numerator // divisor
        divisor = pivot
    return sign * matrix[-1][-1]


def adjacency(n, edges):
    matrix = [[0] * n for _ in range(n)]
    for i, j in edges:
        assert i != j and matrix[i][j] == 0
        matrix[i][j] = matrix[j][i] = 1
    return matrix


def line_inertia(edges):
    line_edges = [(i, j) for i, j in combinations(range(len(edges)), 2)
                  if set(edges[i]).intersection(edges[j])]
    return inertia(adjacency(len(edges), line_edges))


def generate_rooted_trees(limit):
    # Index each unordered rooted tree by the multiset of the IDs of its children.
    trees = [()]
    orders = [1]
    for order in range(2, limit + 1):
        old_count = len(trees)

        def child_multisets(first, left):
            if left == 0:
                yield ()
            for i in range(first, old_count):
                if orders[i] > left:
                    break
                for following in child_multisets(i, left - orders[i]):
                    yield (i,) + following

        for children in child_multisets(0, order - 1):
            trees.append(children)
            orders.append(order)
    return trees


def rooted_edges(trees, root):
    edges = []
    count = 0

    def visit(tree):
        nonlocal count
        parent = count
        count += 1
        for child in trees[tree]:
            vertex = count
            visit(child)
            edges.append((parent, vertex))

    visit(root)
    return count, edges


def check_trees():
    trees = generate_rooted_trees(10)
    assert len(trees) == 1205
    for root in range(len(trees)):
        n, edges = rooted_edges(trees, root)
        matrix = adjacency(n, edges)
        for i in range(n):
            matrix[i][i] = sum(matrix[i]) - 2 + (i == 0)
        pos, zero, neg = inertia(matrix)
        determinant = det(matrix)
        assert zero == 0 and determinant % 2 == 1
        root_inverse = Fraction(det([row[1:] for row in matrix[1:]]), determinant)
        correction = 1 - root_inverse
        loss = neg - pos
        assert loss >= 0
        assert loss != 0 or correction == 0
        assert loss != 1 or correction == 2 or correction < 1
    print(f"rooted trees through order 10, direct cofactor and inertia checks: {len(trees)}")


def kernel_census(n, exceptions_only=False):
    """Enumerate labelled cubic multigraph adjacency matrices. A loop uses two stubs.

    In exceptions_only mode, looped vertices have the first labels. Every possible
    isomorphism type with no simple loopless-to-loopless edge has such a labeling.
    """
    matrix = [[0] * n for _ in range(n)]
    checked = bad = 0

    def complete():
        nonlocal checked, bad
        reached = {0}
        queue = [0]
        while queue:
            current = queue.pop()
            for other, value in enumerate(matrix[current]):
                if value and other not in reached:
                    reached.add(other)
                    queue.append(other)
        if len(reached) != n:
            return
        checked += 1
        if not any(matrix[i][j] == 1 and matrix[i][i] == matrix[j][j] == 0
                   for i, j in combinations(range(n), 2)):
            bad += 1

    for loop_count in range(n + 1):
        loop_sets = [tuple(range(loop_count))] if exceptions_only else combinations(range(n), loop_count)
        for loops in loop_sets:
            remaining = [3] * n
            for i in loops:
                matrix[i][i] = 1
                remaining[i] -= 2

            def fill(row):
                if row == n:
                    complete()
                    return
                if not remaining[row]:
                    fill(row + 1)
                    return
                for columns in combinations_with_replacement(range(row + 1, n), remaining[row]):
                    distinct = set(columns)
                    if any(columns.count(j) > remaining[j] for j in distinct):
                        continue
                    if exceptions_only and row not in loops and any(
                            j not in loops and columns.count(j) == 1 for j in distinct):
                        continue
                    for j in columns:
                        remaining[j] -= 1
                        matrix[row][j] += 1
                        matrix[j][row] += 1
                    fill(row + 1)
                    for j in columns:
                        remaining[j] += 1
                        matrix[row][j] -= 1
                        matrix[j][row] -= 1
            fill(0)
            for i in loops:
                matrix[i][i] = 0
    return checked, bad


def check_kernels():
    for n in (2, 4, 6):
        checked, bad = kernel_census(n)
        assert checked > 0 and (bad > 0 if n <= 4 else bad == 0)
        print(f"all connected labelled cubic multigraphs on {n} vertices: {checked}, without a qualifying edge: {bad}")
    checked, bad = kernel_census(8, exceptions_only=True)
    assert checked == bad == 0
    print("8-vertex cubic multigraphs, exhaustively generating possible exceptions up to relabeling: 0")


def alternating_cycle_chain(c):
    n = 0
    previous = None
    edges = []
    for i in range(c):
        length = 5 if i % 2 == 0 else 4
        edges.extend((n + j, n + (j + 1) % length) for j in range(length))
        if previous is not None:
            edges.append((previous, n))
        previous = n + 1
        n += length
    return n, edges


def check_graphs():
    for c, target in ((2, 1), (3, 2), (4, 2), (5, 3), (6, 3), (7, 4)):
        n, edges = alternating_cycle_chain(c)
        positive, zero, negative = line_inertia(edges)
        assert len(edges) - n + 1 == c
        assert positive - negative == target
        print(f"attaining chain c={c}, order={n}, edges={len(edges)}, line inertia={(positive, zero, negative)}")

    # Independently generate kernels with loops and parallel edges using random
    # pairings and convert each edge to a private subdivided path. Then attach
    # arbitrary rooted trees and evaluate the line graph itself by exact inertia.
    rng = Random(20261126)
    checked = 0
    rooted = generate_rooted_trees(6)
    for b in (2, 4, 6, 8):
        accepted = 0
        while accepted < 30:
            stubs = [v for v in range(b) for _ in range(3)]
            rng.shuffle(stubs)
            links = list(zip(stubs[::2], stubs[1::2]))
            reached = {0}
            for _ in range(b):
                for u, v in links:
                    if u in reached or v in reached:
                        reached.update((u, v))
            if len(reached) != b:
                continue
            accepted += 1
            order = b
            edges = []
            for u, v in links:
                length = rng.randint(3 if u == v else 2, 5)
                internal = list(range(order, order + length - 1))
                path = [u] + internal + [v]
                edges.extend(zip(path, path[1:]))
                order += length - 1
            core_order = order
            for _ in range(rng.randrange(4)):
                host = rng.randrange(core_order)
                size, tree = rooted_edges(rooted, rng.randrange(len(rooted)))
                edges.append((host, order))
                edges.extend((order + u, order + v) for u, v in tree)
                order += size
            c = len(edges) - order + 1
            pos, _, neg = line_inertia(edges)
            assert pos - neg <= b - c + 1
            assert c < 4 or pos - neg <= c - 2
            checked += 1
    print(f"deterministic subdivided cubic kernels with sampled pendant forests, exact line-graph inertia: {checked}")


if __name__ == "__main__":
    check_trees()
    check_kernels()
    check_graphs()
