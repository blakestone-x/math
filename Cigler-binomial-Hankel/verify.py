"""Compare every formula to the original integer Hankel determinants."""

from fractions import Fraction
from functools import cache
from math import comb, factorial


def determinant(matrix):
    """Bareiss elimination including row swaps and singular matrices."""
    n = len(matrix)
    sign, previous = 1, 1
    if not n:
        return 1
    for j in range(n - 1):
        pivot = next((i for i in range(j, n) if matrix[i][j]), None)
        if pivot is None:
            return 0
        if pivot != j:
            matrix[j], matrix[pivot] = matrix[pivot], matrix[j]
            sign = -sign
        row = matrix[j]
        for i in range(j + 1, n):
            target = matrix[i]
            for k in range(j + 1, n):
                numerator = row[j] * target[k] - target[j] * row[k]
                target[k], remainder = divmod(numerator, previous)
                assert not remainder
        previous = row[j]
    return sign * matrix[-1][-1]


@cache
def actual(r, m, n):
    def moment(j):
        return comb(2 * j + r, j) if j >= 0 else 0
    return determinant([[moment(i + j - m) for j in range(n)] for i in range(n)])


def boundary(k, n):
    r = 2 * k - 1
    a = r * (n + 1)
    # Scale each entry in row h by 2^(2h) to eliminate every half-integer.
    def difference(h, center_twice, offset_twice):
        return (center_twice + offset_twice) ** (2 * h) - (
                center_twice - offset_twice) ** (2 * h)
    top = [[difference(h, 2 * a, 2 * j) -
            (difference(h, 2 * a - r, 1) if j == k else 0)
            for j in range(1, k + 1)] for h in range(1, k + 1)]
    base = [[difference(h, r, 2 * j - 1) for j in range(1, k + 1)]
            for h in range(1, k + 1)]
    return Fraction((-1) ** comb(k, 2) * determinant(top), determinant(base))


def verify():
    checks = [0] * 6
    sign = lambda j: (-1) ** comb(j, 2)
    for k in range(1, 7):
        for m in range(-1, 5):
            K = k + m
            for n in range(4):
                r = 2 * K + 1
                assert actual(r, m, r * n) == (2 * n + 1) ** k
                assert actual(r, m, r * n + m + 1) == sign(m + 1) * (2 * n + 1) ** k
                checks[0] += 1
                checks[1] += 1
                if m >= 0:
                    assert actual(r, m, r * n + K + 1) == sign(K + 1) * (4 * (n + 1)) ** k
                    checks[2] += 1
                else:
                    assert actual(r, m, r * n + K + 1) == boundary(k, n)
                    checks[5] += 1
                r = 2 * K
                assert actual(r, m, r * n) == (-1) ** (K * n)
                assert actual(r, m, r * n + m + 1) == sign(m + 1) * (-1) ** (K * n)
                checks[3] += 1
                checks[4] += 1
    print(f"five source identities in their proved ranges {checks[:5]}")
    print(f"boundary evaluations compared with original matrices {checks[5]}")
    for k in range(1, 9):
        degree = 1 if k == 1 else 3 * k - 3
        values = [boundary(k, n) for n in range(degree + 4)]
        for _ in range(degree):
            values = [b - a for a, b in zip(values, values[1:])]
        assert values[0] and len(set(values)) == 1
    print("boundary degrees checked by exact differences for k=1..8")
    print(f"source boundary counterexample {actual(3, -1, 2)} versus predicted -16")


def check_bernoulli():
    bernoulli = {2: Fraction(1, 6), 4: Fraction(-1, 30), 6: Fraction(1, 42)}
    cases = [(2, 0), (2, 1), (2, 2), (2, 3), (3, 0), (3, 1), (3, 2), (4, 0)]
    for k, m in cases:
        K = k + m
        t = 2 * k - 2
        common = -(-1) ** comb(m, 2) * bernoulli[t] / factorial(t)
        for odd in (False, True):
            r = 2 * K + int(odd)
            degree = 3 * k - 3 if odd else 2 * k - 3
            values = [actual(r, m, r * n + m + 2) *
                      (1 if odd else (-1) ** (K * n)) for n in range(degree + 2)]
            for _ in range(degree):
                values = [b - a for a, b in zip(values, values[1:])]
            predicted = common * (2 ** (3 * k - 2) * r ** t if odd
                                  else 4 ** t * K ** (2 * k - 3) * (2 ** t - 1))
            assert values[0] == values[1] == predicted * factorial(degree)
    print(f"Bernoulli leading coefficients tested on original matrices {2 * len(cases)}")
    print("cubic discrepancy at (k,m)=(2,1) satisfies third difference -392")


if __name__ == "__main__":
    verify()
    check_bernoulli()
    print("all exact checks passed")
