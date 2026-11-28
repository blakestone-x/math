"""Independent tree power checks using only NumPy, mpmath and the standard library.

Run with Python 3. Enumerates all labelled trees up to 7 vertices from Prüfer
words. Additional samples include larger trees and paths. Uses exact walk counts
at integer exponents, SVD of the bipartite block for real exponents, and a
high-precision equitable quotient for the large degree constructions.
"""
import heapq
import itertools
import math

import mpmath as mp
import numpy as np


EXPONENTS = (0.5, 1.25, 1.75, 2.25, 2.75, 3.25, 4.5)


def from_prufer(word):
    n = len(word) + 2
    degrees = [1] * n
    for vertex in word:
        degrees[vertex] += 1
    leaves = [i for i, degree in enumerate(degrees) if degree == 1]
    heapq.heapify(leaves)
    edges = []
    for vertex in word:
        leaf = heapq.heappop(leaves)
        edges.append((leaf, vertex))
        degrees[vertex] -= 1
        if degrees[vertex] == 1:
            heapq.heappush(leaves, vertex)
    edges.append(tuple(leaves))
    return edges


def distances_and_blocks(edges):
    n = len(edges) + 1
    dist = np.full((n, n), n, dtype=int)
    np.fill_diagonal(dist, 0)
    adj = np.zeros((n, n), dtype=np.int64)
    for u, v in edges:
        dist[u, v] = dist[v, u] = 1
        adj[u, v] = adj[v, u] = 1
    for i in range(n):
        dist = np.minimum(dist, dist[:, [i]] + dist[[i], :])
    a, b = (np.where(dist[0] % 2 == parity)[0] for parity in (0, 1))
    return dist, a, b, adj


def real_powers(A):
    U, s, Vh = np.linalg.svd(A, full_matrices=False)
    s[s < 1e-12] = 0
    return float(s.max()), [((U * s**(2*p)) @ U.T,
                             (Vh.T * s**(2*p)) @ Vh) for p in EXPONENTS]


def choose_real(x, n):
    return math.prod(x-i for i in range(n)) / math.factorial(n)


def path_envelopes(kmax):
    values = {}
    for k in range(1, kmax + 1):
        # Endpoints of the path have the same color. The discrete sine
        # eigenbasis evaluates each extremal value without SVD.
        n = 2*k + 1
        for p in EXPONENTS:
            if p >= k:
                continue
            value = 0
            for j in range(1, n+1):
                t = math.pi * j/(n+1)
                value += (2/(n+1) * math.sin(t) * math.sin(n*t)
                          * abs(2*math.cos(t))**(2*p))
            values[k, p] = abs(value)
    return values


def verify_tree(edges, envelope, stats):
    n = len(edges) + 1
    dist, a, b, adj = distances_and_blocks(edges)
    block = adj[np.ix_(a, b)]
    r, powers = real_powers(block)
    delta = int(adj.sum(axis=1).max())
    if delta >= 2:
        assert r <= 2*math.sqrt(delta-1) + 1e-11
    for j, vertices in enumerate((a, b)):
        gram = (block @ block.T) if j == 0 else (block.T @ block)
        inside = dist[np.ix_(vertices, vertices)]
        for k in np.unique(inside):
            if not k:
                continue
            selected = np.triu(inside == k, 1)
            pairs = int(selected.sum())
            k = int(k//2)
            # All integer powers through the threshold, computed exactly.
            for m in range(k+1):
                walks = np.linalg.matrix_power(gram, m)[selected]
                assert np.all(walks == (1 if m == k else 0))
                stats["integer cases"] += pairs
            for p, matrices in zip(EXPONENTS, powers):
                vals = matrices[j][selected]
                if p < k:
                    sign = 1 if (-1)**(k+1)*math.sin(math.pi*p) > 0 else -1
                    positive = vals*sign
                    assert np.all(positive > 0)
                    gap = envelope[k,p] - positive
                    if n == 2*k+1:
                        assert np.max(np.abs(gap)) < 1e-9
                    else:
                        assert np.min(gap) > 1e-10
                    stats["subcritical cases"] += pairs
                elif p > k:
                    assert np.all(vals > 0)
                    bound = choose_real(2*p, 2*k)*r**(2*p - 2*k)
                    assert np.all(vals <= bound*(1+1e-11))
                    stats["supercritical cases"] += pairs
    stats["trees"] += 1


def broom_entries(k, leaves):
    # An orthonormal basis for the orbit subspace keeps all path vertices,
    # adding the unit vector that is constant on the new leaves. The
    # orthogonal complement vanishes on both selected endpoints.
    length = 2*k + 1
    B = mp.matrix(length+1)
    for i in range(length-1):
        B[i, i+1] = B[i+1, i] = 1
    B[k, length] = B[length, k] = mp.sqrt(leaves)
    lam, Q = mp.eigsy(B)
    for offset in (mp.mpf(".25"), mp.mpf(".75"), mp.mpf("1.5")):
        power = k + offset
        actual = mp.fsum(abs(lam[j])**(2*power)*Q[0,j]*Q[length-1,j]
                         for j in range(length+1))
        yield float(offset), actual / mp.power(leaves, offset)


def main():
    from collections import Counter
    envelope = path_envelopes(8)
    counts = Counter()
    for n in range(2, 8):
        for word in itertools.product(range(n), repeat=n-2):
            verify_tree(from_prufer(word), envelope, counts)
    print("All labelled trees up through 7 vertices:", dict(counts))
    extra = Counter()
    rng = np.random.default_rng(499788)
    for n in (8, 12, 17):
        for _ in range(60):
            verify_tree(from_prufer(rng.integers(n, size=n-2)), envelope, extra)
        verify_tree([(i,i+1) for i in range(n-1)], envelope, extra)
    print("Additional reproducible samples:", dict(extra))

    mp.mp.dps = 95
    print("Endpoint entries on the broom divided by N^(alpha-k).")
    print("k   alpha-k          N=10^2        N=10^5       N=10^10")
    for k in range(1,6):
        ratios = [dict(broom_entries(k, N)) for N in (10**2,10**5,10**10)]
        for offset in ratios[0]:
            row = [col[offset] for col in ratios]
            assert all(value > 0 for value in row)
            assert abs(row[-1] - 1) < mp.mpf(".03")
            assert abs(row[-1] - 1) < abs(row[0] - 1)
            print(f"{k:1d}     {offset:4.2f}      " +
                  "    ".join(f"{float(value):.10f}" for value in row))


if __name__ == "__main__":
    main()
