#!/usr/bin/env python3
"""Exact graph check for the n=15 deletion obstruction.

This verifies an abstract edge coloring, not a Euclidean point configuration.
"""

from collections import defaultdict

N = 15
VERTICES = range(N)


def circular_difference(a: int, b: int) -> int:
    d = (a - b) % N
    return min(d, N - d)


colors = {j: set() for j in range(1, 8)}
for a in VERTICES:
    for b in range(a + 1, N):
        colors[circular_difference(a, b)].add((a, b))

assert all(len(colors[j]) == 15 for j in colors)

# Move six distinct edges out of color 7, one into each rich color.
moved = sorted(colors[7])[:6]
for j, edge in enumerate(moved, 1):
    colors[7].remove(edge)
    colors[j].add(edge)

assert [len(colors[j]) for j in range(1, 8)] == [16] * 6 + [9]

# Every rich class becomes rare at the new threshold 14 after every
# one-vertex deletion.
for v in VERTICES:
    retained = {
        j: sum(v not in edge for edge in colors[j])
        for j in range(1, 8)
    }
    assert all(13 <= retained[j] <= 14 for j in range(1, 7))
    assert retained[7] <= 9

# Color 7 is a linear forest.
adjacency = defaultdict(list)
for a, b in colors[7]:
    adjacency[a].append(b)
    adjacency[b].append(a)
assert max(map(len, adjacency.values()), default=0) <= 2

seen = set()
for root in VERTICES:
    if root in seen:
        continue
    stack = [(root, -1)]
    while stack:
        vertex, parent = stack.pop()
        assert vertex not in seen, "cycle found"
        seen.add(vertex)
        for neighbor in adjacency[vertex]:
            if neighbor != parent:
                stack.append((neighbor, vertex))

print("PASS: class sizes (16,16,16,16,16,16,9)")
print("PASS: every rich class has 13 or 14 edges after every deletion")
print("PASS: the 9-edge top color is a linear forest")
