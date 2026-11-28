"""Independent finite checks for OEIS A266736, using only the standard library."""
from functools import cache
from fractions import Fraction
from math import comb


def catalan(m):
    return comb(2 * m, m) // (m + 1)


def catalan_sum(n):
    return sum((-2)**j * comb(n, j) * catalan(3*n - j) for j in range(n + 1))


def word_count(n):
    # The two tail values are the least possible last letters of strictly
    # increasing subsequences of lengths one and two. n means absent.
    @cache
    def extend(left, first, second):
        if not any(left):
            return 1
        count = 0
        for a, remaining in enumerate(left):
            if remaining == 0 or a > second:
                continue
            rest = left[:a] + (remaining - 1,) + left[a+1:]
            if a <= first:
                count += extend(rest, a, second)
            else:
                count += extend(rest, first, a)
        return count
    result = extend((3,) * n, n, n)
    extend.cache_clear()
    return result


def coefficient_count(n):
    # (1+z)^(3n) (1+z+z^2+z^3)^n = (1+z)^(4n) (1+z^2)^n.
    def coefficient(i):
        return sum(comb(n,j) * comb(4*n, i-2*j) for j in range(n+1)
                   if 0 <= i-2*j <= 4*n)
    return coefficient(3*n) - coefficient(3*n-1)


def hypergeom(n):
    term = Fraction(1)
    total = term
    for j in range(n):
        term *= Fraction((-1-3*n+j)*(-n+j), (1-6*n+2*j)*(j+1))
        total += term
    return catalan(3*n)*total


if __name__ == '__main__':
    published = [1,1,20,374,8124,190893,4727788,121543500,3212914524,
                 86782926068,2384725558736,66456350375566,1873703883228900,
                 53351152389518550,1531960347453263112,44311785923563130392,
                 1289909841595078198172,37760636720455988917420,1110927659386926734186992]
    assert all(catalan_sum(n) == x for n,x in enumerate(published))
    assert all(word_count(n) == catalan_sum(n) for n in range(8))
    assert all(coefficient_count(n) == hypergeom(n) == catalan_sum(n) for n in range(101))
    print("Direct avoidance counts n=0..7; all 19 published terms; exact identities n=0..100: passed.")
