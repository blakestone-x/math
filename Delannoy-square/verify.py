"""Exact finite checks for weighted and ordinary Delannoy matrix products."""

from fractions import Fraction
from math import comb, lcm


def rows(weight, last):
    table = [[Fraction(1)]]
    for n in range(1, last + 1):
        old = table[-1]
        row = [Fraction(0)] * (n + 1)
        for k, value in enumerate(old):
            row[k] += value
            row[k + 1] += value
        if n >= 2:
            for k, value in enumerate(table[-2]):
                row[k + 1] += weight * value
        table.append(row)
    return table


def endpoint_formula(weight, n, k):
    return sum(comb(k, j) * comb(n - k, j) * (1 + weight) ** j
               for j in range(min(k, n - k) + 1))


def product_row(first, second, n):
    return [sum(first[n][j] * second[j][k] for j in range(k, n + 1))
            for k in range(n + 1)]


def integer_coefficients(polynomial):
    scale = lcm(*(c.denominator for c in polynomial))
    return [int(c * scale) for c in polynomial]


def evaluate_sign(poly, num, den):
    value = poly[-1]
    den_power = 1
    for c in reversed(poly[:-1]):
        den_power *= den
        value = num * value + den_power * c
    return (value > 0) - (value < 0)


def certify(poly, lower, upper):
    """Find degree-many strict sign changes between two negative rationals."""
    coefficients = integer_coefficients(poly)
    n = len(poly) - 1
    divisor = lcm(lower.denominator, upper.denominator)
    left = int(lower * divisor)
    width = int(upper * divisor) - left
    steps = 32
    while steps <= 131072:
        changes = 0
        previous = 0
        for k in range(steps + 1):
            sig = evaluate_sign(coefficients, left * steps + width * k,
                                divisor * steps)
            if sig:
                changes += previous != 0 and sig != previous
                previous = sig
        if changes == n:
            return steps
        steps *= 2
    raise ArithmeticError(f"grid did not isolate row of degree {n}")


def check_source_recurrence(products):
    assert products[:4] == [[1], [2, 1], [5, 6, 1], [12, 25, 10, 1]]
    for n in range(4, len(products)):
        expected = [0] * (n + 1)
        for lag, constant in [(1, 3), (2, -1), (3, -1), (4, 0)]:
            for k, c in enumerate(products[n - lag]):
                expected[k] += constant * c
                expected[k + 1] += c
        assert products[n] == expected


def run(a, b, last, lower, upper):
    a, b = Fraction(a), Fraction(b)
    first, second = rows(a, last), rows(b, last)
    for weight, table in [(a, first), (b, second)]:
        for n in range(last + 1):
            assert table[n] == [endpoint_formula(weight, n, k) for k in range(n + 1)]
    products = [product_row(first, second, n) for n in range(last + 1)]
    if a == b == 1:
        check_source_recurrence(products)
    max_steps = max(certify(polynomial, lower, upper) for polynomial in products[1:])
    print(f"D({a}) D({b}), rows 1 through {last}: all simple negative; "
          f"largest sign grid {max_steps}.")


if __name__ == "__main__":
    # A rational pair of positive weights below the uniform threshold.
    p = product_row(rows(Fraction(1, 16), 3), rows(Fraction(1, 5), 3), 3)
    d, c, b, a = (40 * value for value in p)
    assert [d, c, b, a] == [330, 536, 261, 40]
    assert 18*a*b*c*d - 4*b**3*d + b*b*c*c - 4*a*c**3 - 27*a*a*d*d == -1851464
    print("Weighted cubic counterexample has discriminant -1851464.")
    # The rational interval for the unweighted case is strictly inside the
    # two asserted irrational endpoints; the inequalities follow by squaring.
    run(1, 1, 48, Fraction(-824264, 100000), Fraction(-171573, 1000000))
    for left_weight, right_weight in [(1, Fraction(1, 3)), (2, Fraction(1, 2)),
                                     (Fraction(1, 4), 1), (3, 5)]:
        run(left_weight, right_weight, 22, Fraction(-64), Fraction(-1, 200))
