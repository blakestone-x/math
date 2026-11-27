"""Exact all-width verification for Hardin's constant-stress rectangles (Python 3.10+)."""

import json
from collections import Counter, deque
from functools import cache
from itertools import product
from pathlib import Path

from sympy import Poly, QQ, Symbol, ZZ


X = Symbol("x")


def allowed_masks(q, d):
    """Bit x is set when x from the first column survives this translation."""
    return tuple(sum(1 << x for x in range(q) if (x + b) % (2*d) < q)
                 for b in range(2*d))


def first_state(q):
    full = (1 << q) - 1
    return (full, full, 0, 0)


def next_states(state, masks, d, tilted):
    even, odd, parity, last = state
    following = 1 - parity
    for b in range(2*d):
        if tilted and b % d == last:
            continue
        e = even & masks[b]
        o = odd & masks[(b + following*d) % (2*d)]
        if e and o:
            yield (e, o, following, b % d if tilted else 0)


def word_states(q, d, tilted):
    """All nonempty pairs reachable after one or more column transitions."""
    assert 2*(q-1) < 3*d and q <= 2*d
    masks = allowed_masks(q, d)
    start = first_state(q)
    queue = deque([start])
    visited = {start}
    pairs = set()
    while queue:
        for state in next_states(queue.popleft(), masks, d, tilted):
            pairs.add(state[:2])
            if state not in visited:
                queue.append(state)
                visited.add(state)
    return pairs, len(visited)


def word_layers(q, d, tilted, depth):
    """State multiplicities for each fixed number of column transitions."""
    masks = allowed_masks(q, d)
    counts = Counter({first_state(q): 1})
    for _ in range(depth):
        nxt = Counter()
        for state, mult in counts.items():
            for child in next_states(state, masks, d, tilted):
                nxt[child] += mult
        yield nxt
        counts = nxt


def signature(even, odd, d, tilted):
    if not tilted:
        return ((even.bit_count(), 0), (0, odd.bit_count()))
    by_residue = [((even >> r & 1) + (even >> (r+d) & 1),
                   (odd >> r & 1) + (odd >> (r+d) & 1)) for r in range(d)]
    return tuple(sorted(pair for pair in by_residue if pair != (0, 0)))


def adjacent_lists(shape):
    """Expanded bipartite graph, connecting vertices of distinct residue classes."""
    left = [r for r, (a, _) in enumerate(shape) for _ in range(a)]
    right = [r for r, (_, b) in enumerate(shape) for _ in range(b)]
    offset = len(left)
    return [[offset + j for j, r in enumerate(right) if r != s] for s in left] + [
        [j for j, r in enumerate(left) if r != s] for s in right]


def apply_graph(neighbors, v):
    return [sum(v[j] for j in row) for row in neighbors]


@cache
def graph_polynomial(shape):
    """Minimal monic polynomial on H*1 (positive side lengths), in QQ[x]."""
    neighbors = adjacent_lists(shape)
    v = [len(row) for row in neighbors]
    basis = {}
    for power in range(len(v) + 1):
        w = list(map(QQ.convert, v))
        coeff = [QQ.zero] * power + [QQ.one]
        for pivot, (row, rel) in sorted(basis.items()):
            scale = w[pivot]
            if scale:
                w = [a - scale*b for a, b in zip(w, row)]
                for j, b in enumerate(rel):
                    coeff[j] -= scale*b
        pivot = next((i for i, a in enumerate(w) if a), None)
        if pivot is None:
            poly = Poly.from_list(list(reversed(coeff)), X, domain=QQ)
            return poly.set_domain(ZZ)
        scale = w[pivot]
        basis[pivot] = ([a/scale for a in w], [a/scale for a in coeff])
        v = apply_graph(neighbors, v)
    raise AssertionError("no dependence within the graph dimension")


def shapes_for(pairs, d, tilted):
    return {signature(e, o, d, tilted) for e, o in pairs}


def common_polynomial(shapes):
    result = Poly(1, X, domain=ZZ)
    for shape in sorted(shapes):
        result = result.lcm(graph_polynomial(shape))
    return result


@cache
def walk_count(shape, n):
    neighbors = adjacent_lists(shape)
    v = [1] * len(neighbors)
    for _ in range(n):
        v = apply_graph(neighbors, v)
    return sum(v[:sum(a for a, _ in shape)])


def count_by_words(n, layer, d, tilted):
    return sum(mult * walk_count(signature(e, o, d, tilted), n)
               for (e, o, _, _), mult in layer.items())


def literal_count(n, k, q, d, tilted):
    """Independent enumeration of rows over the original alphabet."""
    rows = [r for r in product(range(q), repeat=k+1)
            if not tilted or all(a != b for a, b in zip(r, r[1:]))]
    neighbors = []
    for a in rows:
        compatible = []
        for j, b in enumerate(rows):
            if tilted and any(u == v for u, v in zip(a, b)):
                continue
            if all(abs(a[i]+b[i+1]-a[i+1]-b[i]) == d for i in range(k)):
                compatible.append(j)
        neighbors.append(compatible)
    v = [1] * len(rows)
    for _ in range(n):
        v = apply_graph(neighbors, v)
    return sum(v)


def high_stress_polynomial(q, d):
    """Closed product for q <= d <= 2q-2."""
    K = 2*q-d
    poly = Poly(1, X, domain=ZZ)
    for a in range(1, K):
        for b in range(a, K-a+1):
            factor = X-a if a == b else X**2-a*b
            poly = poly.lcm(Poly(factor, X, domain=ZZ))
    return poly


def check_catalog():
    catalog = json.loads(Path(__file__).with_name("catalog.json").read_text())
    entries = conjectures = columns = 0
    for row in catalog["tables"]:
        name, q, d, tilted = (row[key] for key in ("table", "q", "d", "tilted"))
        pairs, states = word_states(q, d, tilted)
        shapes = shapes_for(pairs, d, tilted)
        assert (states, len(shapes)) == (row["states"], row["signatures"]), name
        all_poly = common_polynomial(shapes)
        assert all_poly.all_coeffs() == catalog["polynomials"][row["polynomial"]], name

        if q <= d <= 2*q-2:
            assert all_poly == high_stress_polynomial(q, d), name

        # Check the polynomial on each full graph independently of elimination.
        for shape in shapes:
            g = adjacent_lists(shape)
            seed = [len(neighbors) for neighbors in g]
            v = [0] * len(g)
            for c in catalog["polynomials"][row["polynomial"]]:
                v = [a + c*b for a, b in zip(apply_graph(g, v), seed)]
            assert not any(v), (name, shape)

        by_width = {k: (entry, key) for k, entry, key in row["columns"]}
        samples = []
        reference_matched = False
        for k, layer in enumerate(word_layers(q, d, tilted, max(3, *by_width)), 1):
            if k <= 3:
                samples.append([count_by_words(n, layer, d, tilted) for n in range(1, 4)])
            if k in by_width:
                entry, key = by_width[k]
                active = shapes_for({s[:2] for s in layer}, d, tilted)
                polynomial = common_polynomial(active)
                assert polynomial.all_coeffs() == catalog["polynomials"][key], entry
                reference_matched |= entry == row["source_column"] and polynomial == all_poly
                columns += 1
        assert not row["proposed"] or reference_matched, name
        six = [samples[0][0], samples[1][0], samples[0][1],
               samples[2][0], samples[1][1], samples[0][2]]
        assert six == row["samples"], name
        assert all(samples[k][n] == samples[n][k] for k in range(3) for n in range(3)), name
        # Literal alphabet enumeration uses the original square rule.
        assert samples[1][2] == literal_count(3, 2, q, d, tilted), name
        entries += 1
        conjectures += int(row["proposed"])
    print(f"{entries} least all-width polynomials, {conjectures} proposed in the source, "
          f"{columns} fixed-column recurrence statements.")
    print("Every reachable graph passed exact integer polynomial evaluation. "
          "All table prefixes and independent rectangle checks matched.")


if __name__ == "__main__":
    check_catalog()
    assert literal_count(3, 2, 3, 1, True) == 0
    assert literal_count(3, 2, 4, 1, True) == 8
