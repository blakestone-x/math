"""Check the split-prime Legendre reduction directly. Python 3 standard library."""
from math import comb, isqrt


def primes_through(n):
    return [p for p in range(7, n + 1, 6) if all(p % d for d in range(2, isqrt(p) + 1))]


def legendre(n):
    return [(-1)**j * comb(n, j) * comb(n + j, j) for j in range(n + 1)]


def quotient(poly, divisor, p):
    work = [v % p for v in poly]
    inv = pow(divisor[-1], -1, p)
    result = [0] * (len(poly) - len(divisor) + 1)
    for j in reversed(range(len(result))):
        q = work[j + len(divisor) - 1] * inv % p
        result[j] = q
        for i, v in enumerate(divisor):
            work[j + i] = (work[j + i] - q * v) % p
    return result, work[:len(divisor) - 1]


def reduction(p):
    L = (p - 1) // 3
    A = legendre(L)
    C = legendre(2 * L)
    for j, a in enumerate(A):
        C[j] -= a
    assert all(c % p == 0 for c in C)
    C = [c // p * pow(3, -1, p) % p for c in C]
    D, _ = quotient(C, A, p)
    assert sum(D) % p == D[0]
    Cp = [j * c % p for j, c in enumerate(C) if j]
    _, remainder = quotient(Cp, A, p)
    residue = remainder[-1] * pow(A[-1], -1, p) % p
    E = (D[0] + 3 * residue) % p
    a = pow(54, L, p*p) * comb(2*L, L)
    return pow(a, p, p*p) * (1 - p*E) % (p*p)


def original(p):
    m = p*p
    cats = [comb(2*j, j) // (j+1) % m for j in range(2*p-1)]
    h = [sum(comb(n, j)**2 * cats[j] for j in range(n + 1)) % m for n in range(2*p-1)]
    gram = [[h[i+j] for j in range(p)] for i in range(p)]
    det = 1
    for i in range(p):
        r = next(j for j in range(i, p) if gram[j][i] % p)
        if i != r:
            gram[i], gram[r] = gram[r], gram[i]
            det = -det
        pivot = gram[i][i]
        det = det * pivot % m
        inv = pow(pivot, -1, m)
        for row in gram[i+1:]:
            coeff = row[i] * inv % m
            for j in range(i+1, p):
                row[j] = (row[j] - coeff * gram[i][j]) % m
    return (-1)**((p-1)//2) * det % m


if __name__ == '__main__':
    primes = primes_through(199)
    for p in primes:
        assert original(p) == reduction(p), p
    print(f'Legendre reduction agrees with original signed Hankel determinants at all {len(primes)} split primes through 199.')
