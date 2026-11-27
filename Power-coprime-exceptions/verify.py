"""Exact Hamilton-path and divisor checks for Sun's power-coprime labels."""

from functools import cache
from math import gcd, isqrt, lcm, prod


def prime_factors(n):
    result = []
    p = 2
    while p*p <= n:
        if n % p == 0:
            result.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        result.append(n)
    return result


def isprime(n):
    return n >= 2 and all(n % p for p in range(2, isqrt(n)+1))


def forced_sizes(k):
    primes = [p for p in range(2, k+2) if k % (p-1) == 0 and isprime(p)]
    divisors = [1]
    for p in primes:
        divisors += [p*d for d in divisors]
    first = {d-1 for d in divisors if d > 2}
    second = {2*d-1 for d in divisors if d > 2 and d % 2 == 0}
    assert first.isdisjoint(second)
    assert len(first | second) == 3*2**(len(primes)-1)-3
    return primes, first | second


def circle_count(n, k):
    """Count paths 0,...,n with admissible edges, using vertex subsets."""
    modulus = n*n-1
    edges = [sum(1 << y for y in range(1, n)
                 if y != x and gcd(pow(x, k, modulus)+y, modulus) == 1)
             for x in range(n)]
    end = [gcd(pow(x, k, modulus)+n, modulus) == 1 for x in range(n)]
    assert gcd(pow(n, k, modulus), modulus) == 1

    @cache
    def count(x, unused):
        if unused == 0:
            return int(end[x])
        possible, answer = edges[x] & unused, 0
        while possible:
            bit = possible & -possible
            possible ^= bit
            answer += count(bit.bit_length()-1, unused ^ bit)
        return answer

    result = count(0, (1 << n)-2)
    count.cache_clear()
    return result


def check_first_step(n):
    p = prod(prime_factors(n+1))
    m = (n+1)//p
    exists = any(gcd(p*j-1, n*n-1) == 1 for j in range(1, m))
    formula = m == 1 or (m == 2 and p > 2)
    assert exists != formula
    return formula


def main():
    known = [1,0,1,1,0,6,3,42,68,2794,0,5311604,478,57009,2716452,10778632]
    assert [circle_count(n, 2) for n in range(2, 17)] == known[1:]
    print('Exact quadratic counts at n=2,...,16:', *known[1:])
    tested = excluded = 0
    for k in [*range(1, 25), 60, 120]:
        primes, forced = forced_sizes(k)
        for n in range(2, 17):
            count = circle_count(n, k)
            if n in forced:
                assert count == 0
                excluded += 1
            tested += 1
    print(f'{tested} exact power/modulus counts; {excluded} predicted obstructions reconfirmed.')
    for k in (2, 4, 6, 12, 60, 120):
        primes, forced = forced_sizes(k)
        print(f'k={k}, primes={primes}, theorem certifies {len(forced)} exceptional sizes.')
    failed = sum(check_first_step(n) for n in range(2, 50001))
    print(f'Saturated first-step criterion matched the two families for every 2 <= n <= 50000'
          f' ({failed} forced failures).')
    for n in range(2, 101):
        modulus = n*n-1
        period = lcm(*(p-1 for p in prime_factors(modulus)))
        radical = prod(prime_factors(modulus))
        for x in range(n+1):
            for k in range(1, 6):
                assert pow(x, k, radical) == pow(x, k+period, radical)
    print('Exponent periodicity independently checked at every size from 2 through 100.')


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run Python with assertions enabled.')
    main()
