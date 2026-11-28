#!/usr/bin/env python3
"""Exact finite checks for the cyclic joint-realizability obstruction.

The script verifies combinatorial counts and the modular chord argument.
It does not replace the turning-angle proof in cyclic-rigidity.tex.
"""

from math import gcd


def circular_difference(a: int, b: int, n: int) -> int:
    d = (a - b) % n
    return min(d, n - d)


def check(n: int) -> None:
    assert n >= 9 and n % 2 == 1
    t = (n - 1) // 2
    colors = {j: set() for j in range(1, t + 1)}
    for a in range(n):
        for b in range(a + 1, n):
            colors[circular_difference(a, b, n)].add((a, b))

    assert all(len(colors[j]) == n for j in colors)
    moved = sorted(colors[t])[: t - 1]
    for j, edge in enumerate(moved, 1):
        colors[t].remove(edge)
        colors[j].add(edge)

    assert [len(colors[j]) for j in range(1, t + 1)] == [n + 1] * (t - 1) + [t + 2]
    assert sum(map(len, colors.values())) == n * (n - 1) // 2

    degrees = {j: [0] * n for j in colors}
    for j, edges in colors.items():
        for a, b in edges:
            degrees[j][a] += 1
            degrees[j][b] += 1

    for vertex in range(n):
        retained = {
            j: len(colors[j]) - degrees[j][vertex]
            for j in colors
        }
        assert all(retained[j] in (n - 2, n - 1) for j in range(1, t))
        assert retained[t] <= t + 2 <= n - 1

    # If z = exp(2*pi*i*k/n) is primitive, equal chord lengths at
    # differences h and j imply k*h == +/- k*j (mod n).  Check the
    # resulting half-range uniqueness entirely in modular arithmetic.
    for k in range(1, n):
        if gcd(k, n) != 1:
            continue
        for h in range(1, t + 1):
            for j in range(1, t + 1):
                equal = ((k * h - k * j) % n == 0) or ((k * h + k * j) % n == 0)
                assert equal == (h == j)


for order in range(9, 202, 2):
    check(order)

print("PASS: all odd orders 9 through 201")
print("PASS: extremal color counts and every one-vertex deletion")
print("PASS: primitive-root chord classes are distinct in the half-range")
