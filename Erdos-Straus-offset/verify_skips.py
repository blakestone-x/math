"""Check the 119 certificate, the 23 and 31 residue tests, and the 18-value list."""

from math import isqrt, prod


def is_prime(n):
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    return all(n % q != 0 for q in range(3, isqrt(n) + 1, 2))


def prime_divisors(n):
    return {q for q in range(2, n + 1) if n % q == 0 and is_prime(q)}


p = 1_736_718_481
assert is_prime(p) and p % 12 == 1
c_factors = [19, 757, 30_187]
assert all(is_prime(q) and q % 3 == 1 for q in c_factors)
assert 4 * prod(c_factors) == p + 3

small_primes = set().union(*(prime_divisors(a) for a in range(3, 119, 4)))
assert small_primes == {
    3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 43, 47, 59, 67, 71, 79, 83, 103, 107,
}
negative_primes = {q for q in small_primes if pow(p, (q - 1) // 2, q) != 1}
assert negative_primes == {17}
assert [a for a in range(3, 119, 4) if a % 17 == 0] == [51]

x51 = (p*p + 51) // 4
assert x51 == 754_047_770_561_736_853
factorization = {2: 2, 3: 1, 10_341_481: 1, 6_076_239_391: 1}
assert all(is_prime(q) for q in factorization)
assert prod(q**e for q, e in factorization.items()) == x51 - 1
assert pow(5, x51 - 1, x51) == 1
assert all(pow(5, (x51 - 1) // q, x51) != 1 for q in factorization)
assert x51 % 3 == p % 3 == 1

x119, remainder = divmod(p*p + 119, 4)
assert remainder == 0 and x119 == 754_047_770_561_736_870
assert x119 % 30 == 0 and p % 119 == 113
B = p*p*x119
d = 180*p**3
complement, remainder = divmod(B*B, d)
assert remainder == 0 and (p*p*x119*x119) % complement == 0
y, remainder_y = divmod(B + d, 119)
z, remainder_z = divmod(B + complement, 119)
assert remainder_y == remainder_z == 0 and 0 < x119 < y < z
assert y == 19_112_210_958_369_462_542_456_769_164_210_550
assert z == 46_100_736_089_126_345_184_848_832_995_619_949_998_325
assert 4*x119*y*z == p*p*(x119*y + y*z + z*x119)

# Each m in the first row divides x^2 because 6 divides x. In the second
# row, 4 divides x. Check the residue certificate for every nonresidue p.
for a, factors in [(23, [2**i * 3**j for i in range(3) for j in range(3)]),
                   (31, [1, 2, 4, 8, 16])]:
    for residue in range(1, a):
        if pow(residue, (a - 1) // 2, a) == a - 1:
            assert any((4*m*residue**e + residue**4) % a == 0
                       for m in factors for e in (1, 3))

skipped = {3, 27, 35, 55, 63, 75, 91, 99, 115, 119, 123, 131, 135, 139, 143, 147, 151, 155}
impossible = {3, 27, 35, 55, 63, 75, 91, 99, 115, 135, 143, 147, 155}
realized = {119, 123, 131, 139, 151}
assert skipped == impossible | realized and impossible.isdisjoint(realized)
print("Certified the 119 minimum, both nonresidue implications, and the 13/5 accounting.")
