"""Check the A248029 interval criteria for integers up to the chosen limit."""

from argparse import ArgumentParser


def divisor_sums(limit):
    sums = [0] * (limit + 1)
    for divisor in range(1, limit + 1):
        for multiple in range(divisor, limit + 1, divisor):
            sums[multiple] += divisor
    return sums


def smallest_prime_factors(limit):
    primes = list(range(limit + 1))
    for prime in range(2, int(limit**0.5) + 1):
        if primes[prime] == prime:
            for multiple in range(prime * prime, limit + 1, prime):
                if primes[multiple] == multiple:
                    primes[multiple] = prime
    return primes


def prime_powers(n, smallest):
    while n > 1:
        p = smallest[n]
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        yield p, e


def prime_power_witness(n, sums, smallest):
    odd = n // (n & -n)
    two_power = n // odd
    if odd == 1:
        return sums[n] - n
    if smallest[odd] == odd:
        d = sums[n]
        return (d if d <= 2 * n else d // 2) - n

    base = 1
    powers = []
    for p, e in prime_powers(odd, smallest):
        if e % 2 == 0:
            base *= p**e
        else:
            powers.append(p**e)
    if sums[base] > 2 * base:
        return None
    z, d = base, sums[base]
    for power in powers:
        z *= power
        d *= sums[power]
        if d > 2 * z:
            d //= 2
    assert z == odd
    return two_power * (d - z)


def check(limit):
    sums = divisor_sums(limit)
    smallest = smallest_prime_factors(limit)
    phi = list(range(limit + 1))
    for p in range(2, limit + 1):
        if smallest[p] == p:
            for multiple in range(p, limit + 1, p):
                phi[multiple] -= phi[multiple] // p

    dyadic_total = core_total = either_total = 0
    direct_checks = []
    for n in range(2, limit + 1):
        d = sums[n]
        while d > 2 * n and d % 2 == 0:
            d //= 2
        dyadic = d <= 2 * n
        if dyadic:
            assert n < d and sums[n] % d == 0
            dyadic_total += 1
        witness = prime_power_witness(n, sums, smallest)
        if witness is not None:
            assert 1 <= witness <= n
            assert (phi[witness] * sums[n]) % (n + witness) == 0
            core_total += 1
        either_total += dyadic or witness is not None
        if not dyadic and witness is None:
            direct = next(
                (m for m in range(1, n + 1) if (phi[m] * sums[n]) % (n + m) == 0),
                None,
            )
            if direct is None:
                raise AssertionError(f"No original witness for n={n}")
            direct_checks.append((n, direct))
    print(f"Integers tested: {limit - 1}")
    print(f"Dyadic divisor criterion: {dyadic_total}")
    print(f"Nonabundant square core criterion: {core_total}")
    print(f"At least one criterion: {either_total}")
    print(f"Remaining inputs checked by exhaustive search: {len(direct_checks)}")
    for n, direct in direct_checks:
        print(f"  n={n}, least m={direct}")


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("limit", nargs="?", type=int, default=100_000)
    args = parser.parse_args()
    if args.limit < 2:
        parser.error("limit must be at least two")
    check(args.limit)
