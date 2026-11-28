"""Check the coefficient transform, the source sequences, and both odd-prime bounds."""
from itertools import product
from math import comb


def choose(a, k):
    if a >= 0:
        return comb(a, k)
    return (-1)**k * comb(k - a - 1, k)


def original(n, ell):
    return sum((-4)**(n-k)*comb(n, k)*choose(ell+2*k, 2*k)*comb(2*k, k)
               for k in range(n+1))


def convolution(n, tops, signs, modulus=None):
    a, b, c, d = tops
    e, f, g = signs
    left = [choose(a, i)*e**i for i in range(n+1)]
    middle = [choose(b, j)*choose(c, j)*f**j for j in range(n+1)]
    right = [choose(d, k)*g**k for k in range(n+1)]
    if modulus:
        left, middle, right = ([x % modulus for x in column]
                               for column in (left, middle, right))
    total = sum(middle[j]*sum(left[i]*right[n-i-j] for i in range(n-j+1))
                for j in range(n+1))
    return total if modulus is None else total % modulus


def verify():
    transforms = 0
    for n in range(23):
        for ell in range(-20, 31):
            assert original(n, ell) == convolution(n, (ell, ell, ell, 2*(n-ell)), (1, 1, -1))
            transforms += 1
    print(f'{transforms} exact coefficient transformations, including negative upper arguments.')

    # Published OEIS terms from the three companion entries.
    prefixes = {2: [1, 8, 196, 5984, 202276], 3: [1, 16, 828, 53836, 3879404], 4: [1, 26, 2266, 248912, 30319450]}
    for m, terms in prefixes.items():
        assert [original(n, m*n) for n in range(len(terms))] == terms

    cases = [(p, r, n) for p in (3, 5, 7, 11, 13) for r in (1, 2) for n in (1, 2)]
    cases += [(3, 3, 1), (3, 4, 2), (5, 3, 1), (7, 3, 1)]
    total = 0
    for p, r, n in cases:
        high = n*p**r
        low = high//p
        modulus = p**(3*r - int(p == 3))
        for m in range(-5, 8):
            assert (original(high, m*high) - original(low, m*low)) % modulus == 0, (p, r, n, m)
            total += 1
    assert (original(3, 6) - original(1, 2)) % 27 == 9
    print(f'{total} source-family congruences; m=-5 through 7, primes 3 through 13.')
    print('At p=3, m=2, n=r=1 the difference is 5976, congruent to 9 modulo 27.')

    total = 0
    for p, r, n in [(3, 1, 2), (3, 2, 3), (3, 3, 1), (5, 1, 1), (5, 2, 2),
                     (5, 3, 1), (7, 2, 1), (11, 1, 2)]:
        high = n*p**r
        low = high//p
        modulus = p**(3*r - int(p == 3))
        for slopes in [(2, -1, 4, -3), (-3, -2, -1, -4), (1, 2, 3, 1), (0, 4, 2, -1)]:
            for signs in product((-1, 1), repeat=3):
                def value(k):
                    return convolution(k, [s*k for s in slopes], signs, modulus)
                assert value(high) == value(low), (p, r, n, slopes, signs)
                total += 1
    print(f'{total} independent signed-convolution tests, including all eight sign patterns.')


if __name__ == '__main__':
    verify()
