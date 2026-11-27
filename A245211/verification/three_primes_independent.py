"""Independent three-prime check by monotonicity and rational bisection."""

from fractions import Fraction
from functools import cache
from itertools import permutations
from math import isqrt


@cache
def local(a, p):
    return sum(Fraction(a + 1 - j, p**j) for j in range(a + 1))


def primes():
    n = 2
    while True:
        if all(n % d for d in range(2, isqrt(n) + 1)):
            yield n
        n += 1


def integer_roots(exponents):
    target = 1
    for e in exponents:
        target *= e + 1
    target += 1
    roots = set()
    for a, b, c in set(permutations(exponents)):
        for x in primes():
            first = local(a, x)
            if first * local(b, x) * local(c, x) <= target:
                break
            if first * (b + 1) * (c + 1) >= target:
                continue
            for y in primes():
                if y <= x:
                    continue
                second = first * local(b, y)
                if second * local(c, y) <= target:
                    break
                if second * (c + 1) >= target:
                    continue
                lo = y + 1
                hi = 2 * lo
                while second * local(c, hi) > target:
                    hi *= 2
                while lo < hi:
                    mid = (lo + hi) // 2
                    if second * local(c, mid) > target:
                        lo = mid + 1
                    else:
                        hi = mid
                if lo % 2 and second * local(c, lo) == target:
                    roots.add((x, a, y, b, lo, c))
    return roots


if __name__ == "__main__":
    from three_primes import check

    for a in (1, 4, 5, 8, 9):
        values = integer_roots((a, 1, 1))
        assert values == set(check(a)[1])
        print(a, "odd integer roots", len(values))
