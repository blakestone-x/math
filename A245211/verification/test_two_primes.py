"""Cross-check the two-prime verifier's arithmetic against literal sums."""
from two_primes import moment, moment_is_zero_mod_p, primes_through


def literal(base, exponent):
    return sum((j+1) * base**j for j in range(exponent+1))


def main():
    primes = primes_through(101)
    for exponent in range(1, 45):
        for p in primes:
            assert moment(p, exponent, p**exponent) == literal(p, exponent)
            for q in primes:
                assert moment_is_zero_mod_p(q, exponent, p) == (literal(q, exponent) % p == 0)
    equalities = []
    for idx, p in enumerate(primes):
        for q in primes[idx+1:]:
            for a in range(1, 9):
                for b in range(1, 9):
                    n = p**a * q**b
                    proper_sum = sum((i+1)*(j+1)*p**i*q**j
                                     for i in range(a+1) for j in range(b+1)
                                     if (i, j) != (a, b))
                    if proper_sum == n:
                        equalities.append((p, a, q, b))
    assert equalities == [(3, 1, 7, 1)], equalities
    print('Closed formulas agree with direct evaluation through exponent 44 at primes <= 101.')
    print('Direct proper-divisor sums through exponents 8 and primes 101 give', equalities)


if __name__ == '__main__':
    main()
