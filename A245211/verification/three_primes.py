"""Exhaust all triples with exponent multiset {a,1,1}, for the proven a <= 9.
Uses the literal moment polynomials and exact integer arithmetic.
"""

from functools import cache
from itertools import permutations
from math import isqrt


@cache
def prime(p):
    return p >= 2 and all(p % k for k in range(2, isqrt(p) + 1))


def moment(p, a):
    total = 0
    for j in range(a, -1, -1):
        total = total * p + (j + 1)
    return total


def check(a):
    D = 4 * (a + 1)
    counts = [0, 0, 0, 0]
    integer_roots = []
    for i, j, k in sorted(set(permutations((a, 1, 1)))):
        for x in range(i * (D // (i + 1)) + 1, 3 * (D + 1) + 2):
            if not prime(x):
                continue
            xpower = x**i
            A = moment(x, i)
            gap = (D + 1) * xpower - A * (j + 1) * (k + 1)
            if gap <= 0:
                continue
            counts[0] += 1
            lo = max(x, j * (D // (j + 1))) + 1
            hi = 1 + (2 * (D + 1) * xpower) // gap
            for y in range(lo, hi + 1):
                if not prime(y):
                    continue
                counts[1] += 1
                product = A * moment(y, j)
                power = xpower * y**j
                g = (D + 1) * power - (k + 1) * product
                if g <= 0:
                    continue
                z = (k * product + g - 1) // g
                if z <= max(y, k * (D // (k + 1))):
                    continue
                counts[2] += 1
                if z % 2 == 0:
                    continue
                counts[3] += 1
                if product * moment(z, k) == (D + 1) * power * z**k:
                    integer_roots.append((x, i, y, j, z, k))
    return counts, integer_roots


if __name__ == "__main__":
    for a in [1, 4, 5, 8, 9]:
        counts, roots = check(a)
        prime_roots = [row for row in roots if prime(row[4])]
        print(
            a,
            *counts,
            "integer roots",
            [(x, y, z) for x, i, y, j, z, k in roots],
            "prime solutions",
            prime_roots,
            flush=True
        )
        assert not prime_roots
