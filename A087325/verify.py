"""Certify the finite base cases for the minimum in OEIS A087325."""

from array import array
from math import isqrt


def smallest_factors(bound):
    """Store the least prime divisor of each composite. Zero denotes a prime or 1."""
    factors = array("H", [0]) * (bound + 1)
    for prime in range(2, isqrt(bound) + 1):
        if factors[prime]:
            continue
        for multiple in range(prime * prime, bound + 1, prime):
            if not factors[multiple]:
                factors[multiple] = prime
    return factors


def signature(value, factors):
    exponents = []
    while value > 1:
        prime = factors[value] or value
        exponent = 0
        while value % prime == 0:
            value //= prime
            exponent += 1
        exponents.append(exponent)
    return sorted(exponents)


def verify():
    expected = [3, 14, 30, 132, 300, 1320, 3000, 13200, 30000, 132000,
                300000, 1320000]
    limit = max(expected)
    factors = smallest_factors(10 ** len(str(limit)) - 1)
    first = {}
    power_of_ten = 10
    for x in range(1, limit + 1):
        if x == power_of_ten:
            power_of_ten *= 10
        left = signature(x, factors)
        m = sum(left)
        if 1 <= m <= len(expected) and m not in first:
            if left == signature(power_of_ten - x, factors):
                first[m] = x
    actual = [first.get(m) for m in range(1, len(expected) + 1)]
    if actual != expected:
        raise AssertionError((actual, expected))
    print(f"Scanned x = 1 through {limit:,}.")
    print("First terms for m = 1 through 12:", *actual)


if __name__ == "__main__":
    verify()
