"""Exact independent checks of the cubic Franel row theorem. Python 3.10+."""
from fractions import Fraction
from math import comb


def v2(value):
    assert value != 0
    return (value & -value).bit_length() - 1


def odd_part(value):
    return value >> v2(value)


def multinomial_valuation(n):
    return 3 * n.bit_count() - (3 * n).bit_count()


def recurrence_checks(last):
    # (n+1)^2 f[n+1] = (7n^2+7n+2) f[n] + 8n^2 f[n-1].
    previous, current = 0, 1
    checked = 0
    for n in range(last + 1):
        if n <= 120:
            assert current == sum(comb(n, k)**3 for k in range(n + 1))
        q = v2(n + 1)
        u = (n + 1) >> q
        c = multinomial_valuation(n)
        if q >= 4 and (1 << q) - 2 >= c + q - 1:
            assert c == 2*q + 1 + 3*(u - 1).bit_count() - (3*u - 1).bit_count()
            assert v2(current) == c + q - 2, (n, q, u)
            checked += 1
        if n in (1, 3, 7):
            assert v2(current) == {1: 1, 3: 3, 7: 9}[n]
        numerator = (7*n*n + 7*n + 2)*current + 8*n*n*previous
        following, remainder = divmod(numerator, (n + 1)**2)
        assert remainder == 0
        previous, current = current, following
    print('Literal binomial row sums checked for 0 <= n <= 120.')
    print(f'Exact recurrence through n={last}; {checked} qualifying rows checked.')


def normalized_sum(n, bits):
    """f[n]/C[n] modulo 2^bits for rows whose normalized summands are integral."""
    modulus = 1 << bits
    c = multinomial_valuation(n)
    # Beyond this index, the original integer multinomial gives v2(R_j) >= 2j-c.
    last = min(n, (bits + c - 1)//2)
    unit, order, total = 1, 0, 1
    for j in range(last):
        a, b, d, e = n-j, j+1, 3*n-2*j, 3*n-2*j-1
        order += 2 + 3*v2(a) - v2(b) - v2(d) - v2(e)
        divisor = odd_part(b)*odd_part(d)*odd_part(e) % modulus
        unit = -unit*pow(odd_part(a), 3, modulus)*pow(divisor, -1, modulus) % modulus
        assert order >= 0
        if order < bits:
            total = (total + (unit << order)) % modulus
    return total


def limit_residue(bits):
    """Compute 4D modulo 2^bits from its independent harmonic series."""
    total, harmonic = Fraction(0), [Fraction(0)]
    for i in range(1, 131):
        harmonic.append(harmonic[-1] + Fraction(1, i))
    for j in range(1, 65):
        k = j + 1
        term = Fraction(4**k, 2*k*k*comb(2*k, k))
        total += 12*term*(harmonic[2*k] - harmonic[2] - harmonic[j])
    # k>=66: v2(4*t_j*H_i) >= 2k-4*floor(log2(k))-1 for i<=2k.
    assert bits <= 32
    modulus = 1 << bits
    return total.numerator*pow(total.denominator, -1, modulus) % modulus


if __name__ == '__main__':
    recurrence_checks(12000)
    bits = 12
    modulus = 1 << bits
    limit = limit_residue(bits)
    tests = 0
    for q in (6, 9, 12, 18, 32, 64, 127, 256, 512, 1000):
        for u in (1, 3, 5, 17, 255):
            n = (u << q) - 1
            c = multinomial_valuation(n)
            assert (1 << q) - 2 >= c + q - 1
            residue = normalized_sum(n, q + bits)
            assert v2(residue) == q - 2, (q, u)
            if q >= 18:
                assert ((residue >> (q-2))*pow(u, -1, modulus)) % modulus == limit
            tests += 1
    # Check the finite first-order error bound, including q below the 12-bit threshold.
    for q in range(4, 26):
        for u in range(1, 24, 2):
            n = (u << q) - 1
            c = multinomial_valuation(n)
            if (1 << q) - 2 - c < 2*q - 4:
                continue
            depth = min(bits, q-2)
            reduced_modulus = 1 << depth
            residue = normalized_sum(n, q+depth)
            normalized = (residue >> (q-2))*pow(u, -1, reduced_modulus)
            assert (normalized - limit) % reduced_modulus == 0, (q, u)
    print(f'{tests} factorial-sum checks at q=6 through 1000 for five odd multipliers.')
    print(f'4D modulo {modulus} = {limit}; all 35 comparisons at q >= 18 agree.')
