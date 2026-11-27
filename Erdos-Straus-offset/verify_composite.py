"""Verify the exact minimum 123 and the local divisor table using integers."""

from fractions import Fraction
from itertools import product
from math import isqrt, prod


def prime_factors(n):
    """Return all distinct prime factors by complete trial division."""
    factors = []
    divisor = 2
    while divisor <= isqrt(n):
        if n % divisor == 0:
            factors.append(divisor)
            while n % divisor == 0:
                n //= divisor
        divisor += 1
    if n > 1:
        factors.append(n)
    return factors


p = 6_172_024_609
r = 123
assert prime_factors(p) == [p]
assert p % 12 == 1
c_factors = [13, 37, 3_207_913]
c = (p + 3) // 4
assert c == prod(c_factors)
assert all(prime_factors(f) == [f] and f % 3 == 1 for f in c_factors)

for a in range(3, r, 4):
    # Euler's criterion gives (p/f) = +1 at every prime factor of a.
    assert all(pow(p, (f - 1) // 2, f) == 1 for f in prime_factors(a))

x, remainder = divmod(p*p + r, 4)
assert remainder == 0
x_factors = {11: 2, 31: 1, 1493: 1, 1_700_546_198_357: 1}
assert all(prime_factors(f) == [f] for f in x_factors)
assert x == prod(f**e for f, e in x_factors.items())

B = p*p*x
d = 1493*p*x
assert x % 1493 == 0 and (p + 1493) % r == 0
assert (p*p*x*x) % d == 0
B_squared_factors = {p: 4, **{f: 2*e for f, e in x_factors.items()}}
primes = tuple(B_squared_factors)
powers = [range(e + 1) for e in B_squared_factors.values()]
divisors = [prod(f**e for f, e in zip(primes, exponents))
            for exponents in product(*powers)]
assert len(set(divisors)) == 675
qualifying = [v for v in divisors if (B + v) % r == 0]
assert len(qualifying) == 6 and min(qualifying) == d

complement, remainder = divmod(B*B, d)
assert remainder == 0
y, remainder = divmod(B + d, r)
assert remainder == 0
z, remainder = divmod(B + complement, r)
assert remainder == 0
assert 0 < x <= min(y, z)
assert Fraction(4, p*p) == Fraction(1, x) + Fraction(1, y) + Fraction(1, z)

# (offset, residue of p, coefficient, exponent) for d = coefficient * p^exponent.
rows = [
    (7, 3, 1, 3), (7, 5, 2, 1), (7, 6, 2, 1),
    (11, 2, 9, 1), (11, 6, 1, 1), (11, 7, 1, 3), (11, 10, 3, 1),
    (15, 7, 2, 3), (15, 13, 2, 1),
    (39, 7, 2, 1), (39, 19, 5, 3), (39, 28, 50, 1),
    (39, 31, 2, 3), (39, 34, 2, 1), (39, 37, 2, 1),
]
for a, residue, coefficient, exponent in rows:
    assert (4*coefficient*residue**exponent + residue**4) % a == 0

witnesses = {residue: (coefficient, exponent)
             for a, residue, coefficient, exponent in rows if a == 39}
assert set(witnesses) == {r for r in range(1, 39, 3) if pow(r, 6, 13) == 12}
# Representatives for p modulo 8, 5 and 39 cover the parity and factor-5
# conditions, as well as the divisor congruence for the six classes.
for representative in range(1, 8 * 5 * 39):
    if representative % 2 == 0 or representative % 5 not in (1, 4):
        continue
    residue = representative % 39
    if residue in witnesses:
        x = (representative**2 + 39) // 4
        coefficient, exponent = witnesses[residue]
        witness = coefficient * representative**exponent
        assert x % 10 == 0
        assert (representative**2 * x)**2 % witness == 0
        assert (4 * witness + representative**4) % 39 == 0

print("Certified the least offset 123, its smallest divisor witness, and all fifteen table residues.")
