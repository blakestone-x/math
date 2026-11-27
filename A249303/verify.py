"""Compare predicted factor degrees with exact polynomial factorization in SymPy."""
from sympy import Poly, divisors, symbols, totient

x = symbols("x")


def frobenius_degree(q, d):
    e, power = 1, q % d
    while power not in (1, d-1):
        e += 1
        power = power * q % d
    return e


def predicted(m, p):
    s = m
    while s % p == 0:
        s //= p
    mult = m // s
    factors = []
    for d in divisors(s):
        if d >= 3:
            degree = frobenius_degree(p, d)
            factors += [(degree, mult)] * (int(totient(d)) // (2*degree))
    if p % 2 and mult > 1:
        factors.append((1, (mult-1)//2))
    return sorted(factors)


if __name__ == "__main__":
    prev, current = Poly(0, x), Poly(1, x)
    for m in range(1, 41):
        expected = sorted(int(totient(d))//2 for d in divisors(m) if d >= 3)
        factors = current.factor_list()[1]
        assert sorted(f.degree() for f, e in factors for _ in range(e)) == expected
        for p in (2, 3, 5, 7, 11, 13):
            factors = current.set_modulus(p).factor_list()[1]
            assert sorted((f.degree(), e) for f, e in factors) == predicted(m, p)
        prev, current = current, current + prev * Poly(x, x)
    print("Rational factors and all multiplicities in six prime fields checked through m=40.")
