"""Exhaust the finite cases and independently sample the general formula."""
from math import isqrt


def is_prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


if __name__ == "__main__":
    primes = [p for p in range(2, 1001) if is_prime(p)]
    bad_locations, bad_parities = [], []
    for n in range(3, 1001):
        row = [(n % p, p) for p in primes if p < n]
        high = max(remainder for remainder, _ in row)
        winners = [i for i, (r, _) in enumerate(row) if r == high]
        assert len(winners) == 1
        i = winners[0]
        if row[i][1] != next(p for p in primes if 2 * p > n):
            bad_locations.append(n)
        if n > 3:
            assert i > 0
            if row[i-1][0] % 2 != n % 2:
                bad_parities.append(n)
    assert bad_locations == [14]
    assert bad_parities == [9, 21]
    print("Unique winner throughout 3..1000; exceptions exactly 14 and 9,21.")
