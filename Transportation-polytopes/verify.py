"""Exact finite certificates for the transportation-polytope manuscript.

Run with Python 3.8 or later. No third-party libraries are required.
"""
from fractions import Fraction
from math import comb


def coefficients(m):
    result = [comb(m, j) ** 2 for j in range(m + 1)]
    result[1] -= m
    return result


def derivative(coeffs):
    return [j * coeffs[j] for j in range(1, len(coeffs))]


def scaled_evaluation(coeffs, p, q):
    """Return q**degree times the value at p/q, exactly, for q > 0."""
    result = 0
    power = 1
    for coefficient in reversed(coeffs):
        result = p * result + power * coefficient
        power *= q
    return result


def laguerre_numerator(polys, p, q):
    """The numerator after multiplication by q**(2*m-2)."""
    value, first, second = [scaled_evaluation(f, p, q) for f in polys]
    return first * first - value * second


def real_root_witnesses(m):
    h = coefficients(m)
    signs = []
    for j in range(256):
        value = scaled_evaluation(h, -j, 256 - j)
        if value:
            signs.append(1 if value > 0 else -1)
    signs.append((-1) ** m)  # sign at sufficiently large negative input
    return sum(a != b for a, b in zip(signs, signs[1:]))


def direct_table_count(m, t):
    """Fill columns; the state records both partial sums in the two unit rows."""
    counts = {(0, 0): 1}
    for capacity in [2 * t] + [t] * m:
        updated = {}
        for (u, v), count in counts.items():
            for a in range(min(t - u, capacity) + 1):
                for b in range(min(t - v, capacity - a) + 1):
                    continuation = (u + a, v + b)
                    updated[continuation] = updated.get(continuation, 0) + count
        counts = updated
    return counts[t, t]


def check_from_margins():
    # The first 2m+1 counts determine every numerator coefficient.
    m = 12
    dimension = 2 * m
    counts = [direct_table_count(m, t) for t in range(dimension + 1)]
    h = [sum((-1)**i * comb(dimension + 1, i) * counts[j - i]
             for i in range(j + 1)) for j in range(dimension + 1)]
    if h != coefficients(m) + [0] * m:
        raise ArithmeticError('Direct enumeration gives a different numerator')
    print('3 by 13 tables, all 25 Ehrhart numerator coefficients verified')


def main():
    check_from_margins()
    h = coefficients(12)
    dh = derivative(h)
    polys = [h, dh, derivative(dh)]
    witness = Fraction(laguerre_numerator(polys, -1, 5), 5**22)
    if witness != Fraction(-389210787898375728, 2384185791015625):
        raise ArithmeticError('Single-example certificate did not match')
    print('m=12, x=-1/5, Laguerre difference =', witness)

    if coefficients(2) != [1, 2, 1]:
        raise ArithmeticError('Initial factorization failed')
    for m in range(3, 12):
        if real_root_witnesses(m) != m:
            raise ArithmeticError(f'Missing real-root brackets at m={m}')
    print('m=2..11: the factorization and all real-root brackets verified')

    for m in range(12, 256):
        h = coefficients(m)
        dh = derivative(h)
        polys = [h, dh, derivative(dh)]
        if all(laguerre_numerator(polys, -j, 6 * m) >= 0
               for j in range(1, 19)):
            raise ArithmeticError(f'Missing negative Laguerre witness at m={m}')
    print('m=12..255: all 244 negative Laguerre certificates verified')


if __name__ == '__main__':
    main()
