"""Independent enumeration of every cyclic assignment for small r.

Place the prime factors of 2**r+1 directly into labeled positions. Anchor one
prime occurring to exponent 1, if available, to remove duplicate rotations.
Compute the initial entry from the explicit sum, then test each cycle without
modular gap pruning. Abort if a candidate lacks a compositeness witness.
"""
import json
from itertools import combinations_with_replacement
from math import prod
from pathlib import Path


def small_primes(limit):
    return [q for q in range(2, limit + 1)
            if all(q % d for d in range(2, int(q**0.5) + 1))]


def assignments(r, factors):
    bins = [1] * r
    remaining = list(factors)
    for i, (p, e) in enumerate(remaining):
        if e == 1:
            bins[0] = p
            remaining.pop(i)
            break

    def place(i):
        if i == len(remaining):
            yield tuple(bins)
            return
        p, e = remaining[i]
        for positions in combinations_with_replacement(range(r), e):
            for j in positions:
                bins[j] *= p
            yield from place(i + 1)
            for j in positions:
                bins[j] //= p

    yield from place(0)


def direct(r, factors, primes):
    assert prod(p**e for p, e in factors) == 2**r + 1
    count = 0
    matches = set()
    for coefficients in assignments(r, factors):
        count += 1
        first = sum((1 << (r - 1 - k)) * prod(coefficients[:k]) for k in range(r))
        chain = [first]
        for c in coefficients:
            nxt, remainder = divmod(2 * chain[-1] + 1, c)
            assert remainder == 0
            chain.append(nxt)
        assert chain.pop() == first
        if len(set(chain)) < r:
            continue
        if any(any(1 < d < v and v % d == 0 for v in chain) for d in primes):
            continue
        assert sorted(chain) == [3, 7], (r, coefficients, chain)
        matches.add(prod(chain))
    return count, sorted(matches)


if __name__ == '__main__':
    data = json.loads(Path(__file__).with_name('factors.json').read_text())
    primes = small_primes(1000)
    for r in [2] + list(range(3, 26, 2)):
        count, matches = direct(r, data['orders'][str(r)], primes)
        print(r, count, matches, flush=True)
