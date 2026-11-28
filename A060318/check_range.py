"""Exact independent modular check for exponents 2 <= n <= LIMIT."""
from math import comb

LIMIT = 10**9


def contains_two(value):
    while value:
        value, digit = divmod(value, 3)
        if digit == 2:
            return True
    return False


def exceptions(limit):
    # Each residue class of exponents modulo period fixes the k low digits
    # of 2**n - 1. Start with k = 1, and maintain its modulus 3**k.
    period, modulus = 2, 3
    candidates = [n for n in (0, 1) if n <= limit]
    while period <= limit:
        next_modulus = 3 * modulus
        step = pow(2, period, next_modulus)
        children = []
        for n in candidates:
            value = pow(2, n, next_modulus)
            for j in range(3):
                exponent = n + j * period
                if exponent <= limit and (value - 1) // modulus != 2:
                    children.append(exponent)
                value = value * step % next_modulus
        candidates = children
        period *= 3
        modulus = next_modulus

    # Every remaining candidate is now an individual exponent. A digit 2
    # among the low 128 trits certifies its exclusion. Check the full integer
    # for any remaining candidate.
    witness_modulus = 3**128
    return sorted(n for n in candidates
                  if n >= 2 and not contains_two(pow(2, n, witness_modulus) - 1)
                  and not contains_two(2**n - 1))


if __name__ == '__main__':
    result = exceptions(LIMIT)
    assert result == [2, 5, 8], result
    for n, p in zip(result, (5, 7, 7), strict=True):
        m = 2**n - 1
        c = comb(2*m, m) // (m+1)
        assert c % p == 0 and all(c % d != 0 for d in range(2, p))
    print(f'2 <= n <= {LIMIT:,}: exactly {result}; least factors 5, 7, 7.')
