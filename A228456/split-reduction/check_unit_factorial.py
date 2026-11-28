"""Check the two-digit unit-root formula from the original moment sum."""
from math import comb, isqrt


def moment(n, modulus):
    return sum(comb(3*j, j) * comb(2*j, j) * comb(j, n - 2*j)
               * pow(2, n - 2*j, modulus) % modulus
               for j in range((n+2)//3, n//2+1)) % modulus


if __name__ == "__main__":
    primes = [p for p in range(7, 80, 6)
              if all(p % k for k in range(2, isqrt(p)+1))]
    for p in primes:
        n = (p-1)//3
        modulus = p*p
        expected = pow(2, p*n, modulus)*comb(2*n, n) % modulus
        assert moment(modulus-1, modulus) == expected * moment(p-1, modulus) % modulus
    print("Two-digit unit-root formula verified at", primes)
