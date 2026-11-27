"""Exact cyclic-difference and polynomial checks for OEIS A355255. Python 3.10+."""

from collections import Counter


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def rotate(word, shift, n):
    shift %= n
    mask = (1 << n) - 1
    return ((word << shift) & mask) | (word >> (n - shift))


def canonical(word, n):
    return min(rotate(word, shift, n) for shift in range(n))


def direct_orbit(n, word):
    """Trace actual right differences and identify rotations after every step."""
    seen = {}
    while True:
        representative = canonical(word, n)
        if representative in seen:
            return len(seen), seen[representative]
        seen[representative] = len(seen)
        word ^= (word >> 1) | ((word & 1) << (n - 1))


def advance(word, steps, n):
    """Multiply by (1+x)^steps in F2[x]/(x^n-1) via Frobenius."""
    shift = 1
    while steps:
        if steps & 1:
            word ^= rotate(word, shift, n)
        shift = (2 * shift) % n
        steps >>= 1
    return word


def valuation(word, n):
    """Direct polynomial long division by x+1, encoded by the bit mask 3."""
    if word == 0:
        return n
    count = 0
    while word.bit_count() % 2 == 0:
        quotient = 0
        while word.bit_length() >= 2:
            shift = word.bit_length() - 2
            quotient ^= 1 << shift
            word ^= 3 << shift
        require(word == 0, "Polynomial division left a remainder")
        word = quotient
        count += 1
    return count


def check_power_rows():
    for n in (1, 2, 4, 8, 16):
        orbits_by_representative = {}
        distribution = Counter()
        for word in range(1 << n):
            representative = canonical(word, n)
            if representative not in orbits_by_representative:
                orbits_by_representative[representative] = direct_orbit(n, word)[0]
            size = orbits_by_representative[representative]
            require(size == n + 1 - valuation(word, n), f"Valuation at {(n, word)}")
            distribution[size] += 1
        predicted = {1: 1, **{d: 1 << (d - 2) for d in range(2, n + 2)}}
        require(distribution == predicted, f"Distribution at length {n}")
    print("All starting words at lengths 1, 2, 4, 8 and 16 match the valuation formula.")


def check_37():
    period = 87381
    factors = (3, 7, 19, 73)
    require(period == 3 ** 2 * 7 * 19 * 73, "Period factorization")
    certificates = (
        (period, 0x3000, 2),
        (period // 3, 0xe26323afd, 20),
        (period // 7, 0x1b4a5b07e0, 18),
        (period // 19, 0x1434b0a0a0, 12),
        (period // 73, 0x1a50a5f80f, 18),
    )
    for exponent, expected, ones in certificates:
        actual = advance(3, exponent, 37)
        require(actual == expected and actual.bit_count() == ones, f"Residue at {exponent}")
    require(rotate(3, 12, 37) == 0x3000, "Rotation closing the length-37 cycle")
    for q in (1, 2, 4, 8):
        n = 37 * q
        start = advance(1, q, n)
        target = canonical(start, n)
        candidate = period * q
        require(canonical(advance(start, candidate, n), n) == target, f"Return at {n}")
        primes = factors if q == 1 else (2,) + factors
        for prime in primes:
            shorter = advance(start, candidate // prime, n)
            require(canonical(shorter, n) != target, f"Smaller period at {(n, prime)}")
    print("37-bead residues and the exact quotient periods at 37, 74, 148 and 296 agree.")


def check_first_counterexample():
    shorter = [2, 4, 8, 8, 32, 64, 16, 16, 512, 64, 2048, 1024, 512,
               16384, 32, 32, 4096]
    for n in range(1, 38):
        count, first_repeated_index = direct_orbit(n, 1)
        if n & (n - 1) == 0:
            require(count == n + 1, f"Singleton at power-of-two length {n}")
        elif n < 37:
            require(count & (count - 1) == 0, f"Earlier counterexample at {n}")
            if n % 2:
                require(count == shorter[(n - 3) // 2], f"Short table at {n}")
        else:
            require((count, first_repeated_index) == (87382, 1), "Direct orbit at 37")
    require(direct_orbit(5, 13)[0] == 4, "Published five-bead example")
    print("Direct necklace traversal at every length 1..37: first failure at 37.")
    print("The 37-bead orbit visits 87,382 necklaces, with preperiod 1 and period 87,381.")


if __name__ == "__main__":
    check_power_rows()
    check_37()
    check_first_counterexample()
