"""Verify the Tier 3 example and its exact least offset using integer arithmetic."""

from math import isqrt


def small_prime_factors(n):
    """Return the distinct prime factors by trial division."""
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


p = 96_616_332_289
c = 79 * 305_747_887
r = 163
assert small_prime_factors(p) == [p]
assert small_prime_factors(c) == [79, 305_747_887]
assert 79 % 3 == 305_747_887 % 3 == 1
assert 4 * c == p + 3 and c % 3 == 1 and p % 12 == 1

for offset in range(3, r, 4):
    for prime in small_prime_factors(offset):
        assert pow(p, (prime - 1) // 2, prime) == 1

x = (p * p + r) // 4
assert 4 * x - p * p == r
assert x == 2_333_678_916_244_615_994_921
B = p * p * x
d = 331_581_285_817 * p
assert B * B % d == 0
y, y_remainder = divmod(B + d, r)
z, z_remainder = divmod(B + B * B // d, r)
assert y_remainder == z_remainder == 0
assert 0 < x <= min(y, z)
assert 4 * x * y * z == p * p * (x * y + x * z + y * z)
print(f"Certified Tier 3 prime {p:,} and its exact least offset {r}.")
