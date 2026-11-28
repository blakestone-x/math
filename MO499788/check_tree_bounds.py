"""Independent finite check of sign, sharp path constants and equality cases.

Uses NumPy plus the Python standard library. Generate every unlabeled tree
up to the chosen order by successively adding a leaf and deduplicating via
canonical rooted encodings. Check square roots by symmetric diagonalization.
"""
import argparse
import math
from collections import deque
import numpy as np


def rooted_code(tree, vertex, parent):
    children = sorted(rooted_code(tree, v, vertex) for v in tree[vertex] if v != parent)
    return "(" + "".join(children) + ")"


def tree_code(tree):
    degrees = list(map(len, tree))
    leaves = [a for a, deg in enumerate(degrees) if deg <= 1]
    remaining = len(tree)
    while remaining > 2:
        remaining -= len(leaves)
        next_leaves = []
        for a in leaves:
            for b in tree[a]:
                degrees[b] -= 1
                if degrees[b] == 1:
                    next_leaves.append(b)
        leaves = next_leaves
    return min(rooted_code(tree, a, -1) for a in leaves)


def grow(trees):
    new = {}
    for tree in trees:
        for i in range(len(tree)):
            t = [list(row) for row in tree]
            t[i].append(len(tree))
            t.append([i])
            new.setdefault(tree_code(t), t)
    return new.values()


def distances(tree, root):
    d = [-1] * len(tree)
    d[root] = 0
    queue = deque([root])
    while queue:
        v = queue.popleft()
        for w in tree[v]:
            if d[w] == -1:
                d[w] = d[v] + 1
                queue.append(w)
    return d


def powers(tree, alphas):
    A = np.zeros((len(tree), len(tree)))
    for a, row in enumerate(tree):
        A[a,row] = 1
    vals, vecs = np.linalg.eigh(A)
    radii = np.abs(vals)
    radii[radii < 1e-12] = 0
    return [(vecs * radii**(2*alpha)) @ vecs.T for alpha in alphas]


def main(max_n):
    alphas = [0.25, 0.5, 0.75]
    path_values = {}
    for l in range(3, max_n + 1, 2):
        path = [list(range(max(0,i-1),i)) + list(range(i+1,min(i+2,l))) for i in range(l)]
        extremals = [abs(B[0,-1]) for B in powers(path, alphas)]
        b = l+1
        closed = (math.tan(math.pi/(2*b)) + math.tan(3*math.pi/(2*b))) / b
        assert abs(extremals[1] - closed) < 1e-12
        path_values[l-1] = extremals
    trees = [[[]]]
    sizes = [1,1,1,2,3,6,11,23,47,106,235,551,1301,3159,7741]
    counts = np.zeros(3, dtype=np.int64)
    checked = 0
    for n in range(2, max_n+1):
        trees = grow(trees)
        assert len(trees) == sizes[n-1]
        checked += len(trees)
        for t in trees:
            matrices = powers(t, alphas)
            for i in range(n):
                for j, d in enumerate(distances(t,i)):
                    if j <= i or d % 2:
                        continue
                    extremal = d == n-1
                    for h, M in enumerate(matrices):
                        val = (-1)**(d//2+1) * M[i,j]
                        err = path_values[d][h] - val
                        assert val > 0
                        if extremal:
                            assert abs(err) < 1e-12
                        else:
                            assert err > 1e-12
                        counts[h] += 1
    print(f"Checked {checked} nonisomorphic trees of sizes 2 through {max_n}.")
    for alpha, cnt in zip(alphas, counts):
        print(f"alpha={alpha}: checked sign, bound and equality on {cnt} same-color vertex pairs.")
    print("All endpoint square-root values match the closed trigonometric expression.")


if __name__ == "__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--max-n",type=int,default=13,choices=range(3,16))
    main(parser.parse_args().max_n)
