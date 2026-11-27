"""Count bracelet orbits by their number of distinct marked words."""

import argparse
from collections import Counter
from functools import cache
from itertools import product
from math import isqrt
from pathlib import Path


@cache
def divisors(n):
    low = [d for d in range(1, isqrt(n) + 1) if n % d == 0]
    return tuple(low + [n // d for d in reversed(low) if d * d != n])


@cache
def mobius(n):
    return 1 if n == 1 else -sum(mobius(d) for d in divisors(n) if d < n)


def all_symmetric(p, q):
    if p % 2:
        return q ** ((p + 1) // 2)
    return (q + 1) * q ** (p // 2) // 2


@cache
def primitive(p, q):
    necklaces = sum(mobius(d) * q**(p // d) for d in divisors(p)) // p
    achiral = sum(mobius(d) * all_symmetric(p // d, q) for d in divisors(p))
    assert (necklaces - achiral) % 2 == 0
    return achiral, (necklaces - achiral) // 2


def orbit_row(n, q=2):
    row = Counter()
    for p in divisors(n):
        achiral, chiral = primitive(p, q)
        row[p] += achiral
        row[2*p] += chiral
    return +row


@cache
def b(n):
    return sum(orbit_row(n).values()) - primitive(n, 2)[1]


@cache
def proposed_diagonal(k):
    return sum(mobius(d) * b(k // d) for d in divisors(k))


def classified_good(n):
    if n in (9, 15, 25):
        return True
    odd = n
    while odd % 2 == 0:
        odd //= 2
    return odd == 1 or (n // odd in (1, 2, 4) and len(divisors(odd)) == 2)


def binary_orbits(n):
    mask = (1 << n) - 1
    seen = bytearray(1 << n)
    row = Counter()
    for w in range(1 << n):
        if seen[w]:
            continue
        u = w
        v = int(f'{w:0{n}b}'[::-1], 2)
        orbit = set()
        for _ in range(n):
            orbit.update((u, v))
            u = ((u << 1) & mask) | (u >> (n - 1))
            v = ((v << 1) & mask) | (v >> (n - 1))
        for x in orbit:
            seen[x] = 1
        row[len(orbit)] += 1
    return row


def ternary_orbits(n):
    seen = set()
    row = Counter()
    for word in product(range(3), repeat=n):
        if word in seen:
            continue
        orbit = {w[i:] + w[:i] for w in (word, word[::-1]) for i in range(n)}
        seen.update(orbit)
        row[len(orbit)] += 1
    return row


def check(source=None):
    for n in range(1, 22):
        assert orbit_row(n) == binary_orbits(n), n
    for n in range(1, 10):
        assert orbit_row(n, 3) == ternary_orbits(n), n
    for n in range(1, 1001):
        row = orbit_row(n)
        assert sum(k * count for k, count in row.items()) == 2**n
        literal_agreement = all(row[k] == (proposed_diagonal(k) if n % k == 0 else 0)
                                for k in range(1, n + 1))
        assert literal_agreement == classified_good(n), n
        off_divisors = {k for k in row if k <= n and n % k}
        assert off_divisors == {2*p for p in divisors(n) if p >= 6 and n//p % 2 and n//p >= 3}
    assert [orbit_row(n)[k] for n,k in [(18,12),(18,18),(21,14),(21,21)]] == [1,742,2,2030]
    assert [proposed_diagonal(k) for k in (18, 21)] == [743,2032]
    print('All binary orbits through length 21 and ternary orbits through length 9 agree.')
    print('All row classifications, exceptional sizes and weighted sums through length 1000 agree.')
    if source:
        lines = (source / 'seq/A203/A203399.seq').read_text().splitlines()
        expected = [int(x) for line in lines if line[:2] in ('%S', '%T', '%U')
                    for x in line.split(maxsplit=2)[2].split(',') if x]
        actual = (orbit_row(n)[k] for n in range(1, len(expected)+1) for k in range(1, 2*n+1))
        assert all(x == y for x, y in zip(expected, actual))
        print(f'All {len(expected)} terms of the OEIS entry agree.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--oeis-repo', type=Path, help='checkout of oeis/oeisdata')
    check(parser.parse_args().oeis_repo)
