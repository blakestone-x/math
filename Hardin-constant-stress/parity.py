"""Checks for the median and six-difference rectangle theorems."""

from collections import Counter
from itertools import product


def median_count(n, k, q):
    return q**(n+1) + q**(k+1) - q + q*(q-1)*(2**n-1)*(2**k-1)


def shift_mask(mask, b, target):
    return sum(1 << c for c in range(4)
               if mask & (1 << c) and (1 << c) ^ b in target)


def six_layers(depth):
    """Phase words over four parity coordinates. Each label is a unit vector."""
    target = {1, 2, 4, 8}
    charge = 1 ^ 8
    counts = Counter({(15, 15): 1})
    for j in range(1, depth + 1):
        nxt = Counter()
        for (e, o), mult in counts.items():
            for b in range(16):
                left = shift_mask(e, b, target)
                right = shift_mask(o, b ^ (charge if j % 2 else 0), target)
                if left and right:
                    nxt[left, right] += mult
        yield nxt
        counts = nxt


def six_count(n, layer):
    total = 0
    for (e, o), mult in layer.items():
        a, b = e.bit_count(), o.bit_count()
        total += mult * a**(n//2+1) * b**((n+1)//2)
    return total


def literal(n, k, q, six=False):
    rows = list(product(range(q), repeat=k+1))
    edges = []
    for a in rows:
        neighbors = []
        for j, b in enumerate(rows):
            allowed = True
            for t in range(k):
                u, v, w, z = sorted((a[t], a[t+1], b[t], b[t+1]))
                allowed = (3*(z-u)+w-v == 9) if six else (u+w == v+z)
                if not allowed:
                    break
            if allowed:
                neighbors.append(j)
        edges.append(neighbors)
    counts = [1] * len(rows)
    for _ in range(n):
        counts = [sum(counts[j] for j in neighbors) for neighbors in edges]
    return sum(counts)


def check():
    for q in (2, 3, 4, 5):
        for n, k in ((1, 1), (2, 2), (3, 2), (2, 3)):
            assert literal(n, k, q) == median_count(n, k, q)
    for k, layer in enumerate(six_layers(7), 1):
        sizes = {(e.bit_count(), o.bit_count()) for e, o in layer}
        assert sizes <= {(4, 2), (2, 4), (2, 2), (1, 2), (2, 1), (1, 1)}
        if k <= 3:
            assert literal(3, k, 4, six=True) == six_count(3, layer)
        block = [six_count(n, layer) for n in range(1, 16)]
        c = [3, 8, -30, 4, 48, -32]
        for n in range(6, len(block)):
            assert block[n] == sum(a*b for a, b in zip(c, reversed(block[:n])))
    print("Median and six-difference formulas match literal grids and the parity calculation.")


if __name__ == "__main__":
    check()
