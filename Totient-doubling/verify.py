"""Construct complete inverse-totient fibers and check the classification."""
from fractions import Fraction
from math import isqrt


def is_prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def inverse_limit(cap):
    # x <= 2 phi(x)^2. If x has t prime divisors, their product is
    # at least the t-th primorial and x/phi(x) <= the initial Euler product.
    primorial = 1
    ratio = Fraction(1)
    p = 2
    while True:
        if is_prime(p):
            if primorial * p > 2 * cap**2:
                return int(cap * ratio)
            primorial *= p
            ratio *= Fraction(p, p - 1)
        p += 1


def fibers_through(cap):
    limit = inverse_limit(cap)
    phi = list(range(limit + 1))
    for p in range(2, limit + 1):
        if phi[p] == p:
            for multiple in range(p, limit + 1, p):
                phi[multiple] -= phi[multiple] // p
    fibers = [[] for _ in range(cap + 1)]
    for x in range(1, limit + 1):
        if phi[x] <= cap:
            fibers[phi[x]].append(x)
    return limit, fibers


def main():
    cap = 100000
    limit, fibers = fibers_through(cap)
    paired = set()
    for v in range(1, cap + 1):
        fiber = fibers[v]
        odd = [x for x in fiber if x % 2]
        even = [x for x in fiber if x % 2 == 0]
        pairs = bool(fiber) and even == [2 * x for x in odd]
        half = fibers[v // 2] if v % 2 == 0 else []
        assert pairs == (bool(fiber) and not half)
        assert pairs == (bool(fiber) and len(odd) == len(even))
        assert len(fiber) == 2 * len(odd) + sum(x % 2 == 0 for x in half)
        if pairs:
            paired.add(v)
    assert fibers[4] == [5, 8, 10, 12] and 4 not in paired
    reference = [1,6,10,18,22,28,30,42,46,52,54,58,66,70,78,82,100,102,106,110,
                 126,130,136,138,148,150,162,166,172,178,180,190,196,198,210,222,
                 226,228,238,250,262,268,270,282,292,294,306,310,316,330,342,346,
                 348,358,366,372]
    assert sorted(v for v in paired if v <= reference[-1]) == reference
    for core in range(1, cap + 1, 2):
        v = core
        started = False
        while v <= cap:
            assert (v in paired) == (bool(fibers[v]) and not started)
            if started:
                assert fibers[v]
            started |= bool(fibers[v])
            v *= 2

    for p in range(3, cap // 2 + 1, 2):
        if not is_prime(p):
            continue
        candidates = []
        if (p - 1) & (p - 2) == 0 and (p - 1) * p <= cap:
            candidates.append((p - 1) * p)
        v = 2 * p
        while v <= cap:
            if is_prime(v + 1):
                candidates.append(v)
            v *= 2
        v = p
        while v <= cap:
            assert (v in paired) == (bool(candidates) and v == min(candidates))
            v *= 2
        power = p
        while 2 * power <= cap:
            assert bool(fibers[2 * power]) == (p == 3 or is_prime(2 * power + 1))
            power *= p
    print(f"Complete inverse sieve through target {cap:,}, with proven argument bound {limit:,}.")
    print(f"Verified all {len(paired):,} paired values, the fiber-count identity, and every doubling ray in range.")
    print(f"Matched all {len(reference)} terms listed through 372 in A376927; verified the full fiber at 4.")
    print("Verified the prime odd-part and prime-power-level criteria throughout the same range.")


if __name__ == "__main__":
    main()
