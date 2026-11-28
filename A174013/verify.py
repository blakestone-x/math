"""Exact certificates for the three Deléham recurrence formulas. Requires SymPy."""
import sympy as sp

x, t, n = sp.symbols("x t n")


def certificate(u):
    denominator_factor = 1 - u * x
    discriminant = denominator_factor**2 + 4 * u * x**3
    numerator = (u + 2) * x - 1
    denominator = 2 * x * denominator_factor
    first = discriminant * denominator_factor
    zeroth = (2 * discriminant * sp.diff(denominator, x)
              - sp.diff(discriminant, x) * denominator) / 4
    right = (2 * discriminant * sp.diff(numerator, x)
             - sp.diff(discriminant, x) * numerator) / 4
    return [sp.Poly(poly, x) for poly in (first, zeroth, right, discriminant)]


def coefficients(u):
    first, zeroth, right, _ = certificate(u)
    span = max(first.degree(), zeroth.degree())
    return [sp.expand((n - i) * first.nth(i) + zeroth.nth(i))
            for i in range(span + 1)], right


def verify_symbolic():
    expected = [n + 1, -3*t*n, 3*t**2*(n-1),
                -t*((t**2-4)*n-2*t**2+14), -2*t**2*(2*n-7)]
    actual, right = coefficients(t)
    assert all(sp.expand(a-e) == 0 for a, e in zip(actual, expected, strict=True))
    assert right == sp.Poly(1-t*x+3*t*x**2-(t**2+2*t)*x**3, x)
    discriminant = certificate(t)[3]
    assert sp.factor(sp.discriminant(discriminant.as_expr(), x)) == -16*t**2*(t**2+27)
    assert sp.factor(discriminant.eval(1/t)) == 4/t**2

    short, right = coefficients(1+x)
    assert short == [n+1, -3*n, 0, 9*n-24, -6, 46-11*n, -5*n+25]
    assert right == sp.Poly(1-x+3*x**2-6*x**4, x)
    quartic = certificate(1+x)[3]
    assert sp.discriminant(quartic.as_expr(), x) == 20224
    assert sp.gcd(quartic, sp.Poly(1-x-x**2, x)).degree() == 0
    long = [n+1, n, 12*(1-n), 3*(3*n-8), 6*(6*n-23),
            11*(2-n), 253-49*n, 20*(6-n)]
    shifted = [0] + [4 * c.subs(n, n-1) for c in short]
    assert all(sp.expand(a+b-c) == 0
               for a, b, c in zip(short+[0], shifted, long, strict=True))


def from_quadratic(constant, linear, limit):
    """Coefficient recursion for x(1-ux)F^2+(1-(u+2)x)F+x-1=0."""
    sequence = [1]
    squared = [1]
    def at(values, index):
        return values[index] if index >= 0 else 0
    for k in range(1, limit+1):
        term = (-(k == 1) + (constant+2)*at(sequence, k-1)
                + linear*at(sequence, k-2) - at(squared, k-1)
                + constant*at(squared, k-2) + linear*at(squared, k-3))
        sequence.append(term)
        squared.append(sum(sequence[i]*sequence[k-i] for i in range(k+1)))
    return sequence


if __name__ == "__main__":
    verify_symbolic()
    cases = [
        ((1, 0), [1, 1, 2, 3, 4, 4, 2, -3]),
        ((2, 0), [1, 2, 6, 16, 40, 92, 192, 352]),
        ((1, 1), [1, 1, 3, 6, 12, 22, 37, 56]),
    ]
    for (constant, linear), prefix in cases:
        sequence = from_quadratic(constant, linear, 96)
        assert sequence[:len(prefix)] == prefix
        recurrence, _ = coefficients(constant + linear*x)
        for k in range(len(recurrence)-1, len(sequence)):
            assert sum(c.subs(n,k)*sequence[k-j] for j,c in enumerate(recurrence)) == 0
    print("Exact recurrence, shift factorization and discriminant checks passed.")
    print("All three quadratic-series coefficient checks passed through n=96.")
