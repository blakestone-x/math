"""Exact independent checks for the Eulerian edge formulas and limiting polynomials."""
from fractions import Fraction as F
from itertools import combinations, permutations
from math import comb, factorial, prod

from verify import euler_triangle, multiply


def check_inputs():
    triangle = euler_triangle(20)
    for n in range(1, 9):
        counts = [0] * (n+1)
        for permutation in permutations(range(n)):
            descents = sum(permutation[k] > permutation[k+1] for k in range(n-1))
            counts[descents+1] += 1
        assert counts == triangle[n]
    for n in range(1, 21):
        for k in range(1, n+1):
            total = sum((-1)**j * comb(n+1, j) * (k-j)**n for j in range(k+1))
            assert total == triangle[n][k] == triangle[n][n+1-k]
            assert total <= k**n
        assert sum(triangle[n]) == factorial(n)
    print('Permutation enumeration through 8 and independent Eulerian formulas through 20 agree.')


def from_compositions(r, s, h):
    value = F(0)
    for indices in combinations(range(r), h):
        parts = [s+(i in indices) for i in range(r)]
        value += prod(F(1, (v+1)**sum(parts[:i])) for i, v in enumerate(parts))
    return value


def check_limits():
    count = 0
    for r in range(1, 8):
        for s in range(9):
            a, b = s+1, s+2
            lam = F(a, b)
            q = a*lam**s
            elementary = [F(1)]
            for i in range(r):
                elementary.append(F(0))
                for j in range(i+1, 0, -1):
                    elementary[j] += q**i * elementary[j-1]
            base = F(1, a**(s*comb(r, 2)))
            for h in range(r+1):
                closed = base*lam**comb(h, 2)*elementary[h]/a**((r-1)*h)
                assert closed == from_compositions(r, s, h)
                count += 1
    print(f'{count} edge constants agree with independent sums over maximizing compositions.')


def rational_sign(coefficients, value):
    # Coefficients are in ascending degree; value is the positive magnitude.
    p, q = value.numerator, value.denominator
    z = coefficients[-1]
    scale = 1
    for coefficient in reversed(coefficients[:-1]):
        scale *= q
        z = coefficient*scale-p*z
    return (z > 0)-(z < 0)


def check_square_edges():
    # Isolate the three displayed scales at one moderately large index.
    n = 128
    triangle = euler_triangle(n)
    row = multiply(triangle, triangle)[n][1:]
    for lower, upper in ((F(29,100), F(30,100)), (F(170,100), F(172,100))):
        assert rational_sign(row, 2**n * lower) * rational_sign(row, 2**n * upper) == -1
    # A dyadic approximation to (log 2)^(n+1), used solely to choose a bracket.
    from decimal import Decimal, localcontext
    with localcontext() as ctx:
        ctx.prec = 60
        shift = 120
        middle = int(Decimal(2).ln()**(n+1)*2**shift)
    c = F(middle, 2**shift)
    assert rational_sign(row, c*F(99,100))*rational_sign(row, c*F(101,100)) == -1
    print('Three exact sign brackets at row 128 agree with the two extremes and the near-zero scale.')


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run with Python assertions enabled.')
    check_inputs()
    check_limits()
    check_square_edges()
