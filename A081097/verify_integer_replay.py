#!/usr/bin/env python3
"""Independent integer replay for the A081097 proof package.

This script is supporting verification. The infinite theorem is in Lean.
All tests, including the literal nested-floor predicate, use exact integers.
"""
from math import isqrt

SEEDS = ((4, 2), (29, 13), (114, 51), (199, 89))
SOURCE_TERMS = (
    1, 6, 23, 40, 273, 1870, 7343, 12816, 87841, 602070,
    2364359, 4126648, 28284465, 193864606, 761316191, 1328767776,
    9107509825, 62423800998, 245141449079, 427859097160,
    2932589879121, 20100270056686, 78934785287183,
)


def step(pair):
    x, y = pair
    return 161 * x + 360 * y, 72 * x + 161 * y


def back(pair):
    x, y = pair
    return 161 * x - 360 * y, 161 * y - 72 * x


def valid(pair):
    x, y = pair
    return x >= 0 and y >= 0 and x % 5 == 4 and x*x - 5*y*y in (-4, -9)


def literal(n):
    # floor(sqrt(5)*n) = isqrt(5*n*n), and likewise for the outer floor.
    y = isqrt(5*n*n)
    return n > 0 and isqrt(5*n*n*y*y) == 5*n*n - n


def main():
    reduced = tuple((x, y) for x in range(483) for y in range(217)
                    if valid((x, y)))
    assert reduced == SEEDS, reduced
    assert all(back(step(s)) == s and step(back(s)) == s for s in SEEDS)

    block = SEEDS
    terms = []
    for _ in range(50):
        for point in block:
            assert valid(point)
            x, y = point
            n = (x + 1) // 5
            assert 5*n - 1 == x and literal(n)
            terms.append(n)
            q = point
            while q[0] >= 483:
                prev = back(q)
                assert valid(prev) and 0 <= prev[0] < q[0]
                q = prev
            assert q in SEEDS
        block = tuple(map(step, block))
    assert tuple(terms[:len(SOURCE_TERMS)]) == SOURCE_TERMS
    assert all(a < b for a, b in zip(terms, terms[1:]))
    assert all(terms[j+8] == 322*terms[j+4] - terms[j] - 64
               for j in range(len(terms)-8))

    limit = 1_000_000
    direct = tuple(n for n in range(1, limit+1) if literal(n))
    predicted = tuple(n for n in terms if n <= limit)
    assert direct == predicted, (direct, predicted)

    # Exact coefficient identity for (1-z)(1-322z^4+z^8) A(z).
    a = [0] + terms
    coeffs = []
    for j in range(len(a)):
        coeffs.append(sum(c*a[j-shift] for shift, c in
                          ((0, 1), (1, -1), (4, -322), (5, 322), (8, 1), (9, -1))
                          if j >= shift))
    assert coeffs[:9] == [0, 1, 5, 17, 17, -89, -13, -1, -1]
    assert not any(coeffs[9:])
    print("PASS: four reduced seeds; exact source terms; 200 ordered orbit terms;")
    print("      literal nested-floor replay through n=1,000,000; recurrence and GF coefficients.")


if __name__ == "__main__":
    main()
