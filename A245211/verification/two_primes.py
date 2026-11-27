"""Check all fixed points p**a*q**b with p<q and 1<=b<=LIMIT.

The proven exponent and prime bounds are in the accompanying research note.
Only Python's standard library is required.
"""
import argparse
from bisect import bisect_right
from math import isqrt


def primes_through(limit):
    sieve = bytearray([1]) * (limit + 1)
    sieve[:2] = bytes(2)
    for prime in range(2, isqrt(limit) + 1):
        if sieve[prime]:
            start = prime * prime
            sieve[start::prime] = bytes((limit - start) // prime + 1)
    return [n for n in range(2, limit + 1) if sieve[n]]


def moment(p, exponent, power):
    numerator = power * p * ((exponent + 1) * p - (exponent + 2)) + 1
    return numerator // ((p - 1) ** 2)


def moment_is_zero_mod_p(q, b, p):
    u = q % p
    if u == 1:
        return (b + 1) * (b + 2) // 2 % p == 0
    numerator = pow(u, b + 1, p) * ((b + 1) * u - (b + 2)) + 1
    return numerator % p == 0


def run(limit):
    primes = primes_through(6 * limit * (limit + 1))
    pairs = candidates = exact_checks = 0
    found = []
    for b in range(1, limit + 1):
        for a in range(b, 3 * b):
            pairs += 1
            degree = (a + 1) * (b + 1)
            # Every fixed point here is odd. Thus the moments modulo 2
            # equal the triangular numbers (a+1)(a+2)/2 and (b+1)(b+2)/2.
            if ((a+1)*(a+2)//2 * ((b+1)*(b+2)//2) - (degree+1)) % 2:
                continue
            lo = bisect_right(primes, a * (b + 1))
            hi = bisect_right(primes, 2 * degree)
            for p in primes[lo:hi]:
                candidates += 1
                power = p ** a
                value = moment(p, a, power)
                gap = (degree + 1) * power - (b + 1) * value
                if gap <= 0:
                    continue
                q = (b * value + gap - 1) // gap
                if q <= p or q % 2 == 0 or not moment_is_zero_mod_p(q, b, p):
                    continue
                exact_checks += 1
                qpower = q ** b
                if value * moment(q, b, qpower) == (degree + 1) * power * qpower:
                    # No prime test is needed to disqualify a candidate. Preserve
                    # every equality, even if it were to have a composite q.
                    found.append((p, a, q, b))
        if b % 20 == 0 or b == limit:
            print(f'b <= {b}: {pairs} exponent pairs; {candidates} prime candidates; '
                  f'{exact_checks} full equalities tested; matches {found}', flush=True)
    if found != [(3, 1, 7, 1)]:
        raise RuntimeError(f'Unexpected equality list: {found}')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('limit', type=int, nargs='?', default=100)
    args = parser.parse_args()
    if args.limit < 1:
        parser.error('limit must be positive')
    run(args.limit)
