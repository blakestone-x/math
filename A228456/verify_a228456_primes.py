"""Check the determinant congruences directly, starting with Catalan numbers."""
from math import comb, isqrt

BOUND = 151


def primes():
    for p in range(5, BOUND + 1):
        if all(p % j for j in range(2, isqrt(p) + 1)):
            yield p


def leading_determinant(residues, p):
    modulus = p**2
    matrix = [residues[row:row + p] for row in range(p)]
    product = 1
    for col in range(p - 1):
        pivot = next(row for row in range(col, p) if matrix[row][col] % p)
        if pivot != col:
            matrix[pivot], matrix[col] = matrix[col], matrix[pivot]
            product = -product
        pivot_row = matrix[col]
        product = product * pivot_row[col] % modulus
        inv = pow(pivot_row[col], -1, modulus)
        for row in matrix[col + 1:]:
            multiplier = row[col] * inv % modulus
            if multiplier:
                for j in range(col + 1, p):
                    row[j] = (row[j] - multiplier * pivot_row[j]) % modulus
    return product * matrix[-1][-1] % modulus


def signed_x(p):
    for y in range(1, isqrt(p // 3) + 1):
        x = isqrt(p - 3 * y * y)
        if x * x + 3 * y * y == p:
            return x if x % 3 == 1 else -x
    raise ArithmeticError('missing representation')


def main():
    catalans = [comb(2 * j, j) // (j + 1) for j in range(2 * BOUND)]
    h = [sum(comb(n, j)**2 * catalans[j] for j in range(n + 1))
         for n in range(2 * BOUND)]
    inert, split = [], []
    for p in primes():
        modulus = p**2
        residues = [n % modulus for n in h[:2 * p - 1]]
        signed = (-1)**((p - 1) // 2) * leading_determinant(residues, p) % modulus
        if p % 3 == 2:
            binom = comb((p + 1) // 2, (p + 1) // 6)
            assert (binom * signed + 3 * p) % modulus == 0
            inert.append(p)
        else:
            assert (signed - 2 * signed_x(p)) % p == 0
            split.append(p)
    print('Inert primes checked modulo p^2:', inert)
    print('Split primes checked modulo p:', split)


if __name__ == '__main__':
    main()
