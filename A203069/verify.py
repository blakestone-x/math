"""Certify the uniform linear bound and enumerate the first square-sum exception."""
from itertools import combinations, count
from math import gcd, isqrt


def prime(n):
    if n % 2 == 0:
        return n == 2
    return n > 1 and all(n % d for d in range(3, isqrt(n) + 1, 2))


def greedy(degree, length):
    terms = [1]
    used = {1}
    first_unused = [2, 3]
    for position in range(2, length + 1):
        parity = position % 2
        previous_power = terms[-1] ** degree
        for candidate in count(first_unused[parity], 2):
            if candidate not in used and not prime(previous_power + candidate ** degree):
                break
        terms.append(candidate)
        used.add(candidate)
        while first_unused[parity] in used:
            first_unused[parity] += 2
    return terms


def linear_bound():
    length, wheel = 1501, 15015
    primes = [17, 19, 23, 29, 31, 37]
    prefix = [0]
    for i in range(2*wheel):
        prefix.append(prefix[-1] + (gcd(i, wheel) == 1))

    def counts(h):
        return (prefix[s+h] - prefix[s] for s in range(wheel))

    largest = max(counts(length))
    removed = [min(counts(length//p)) for p in primes]
    overlaps = sum(max(counts((length + p*q - 1)//(p*q)))
                   for p, q in combinations(primes, 2))
    assert removed == [28, 26, 20, 15, 15, 12]
    assert (largest, sum(removed), overlaps) == (580, 116, 35)
    assert largest - sum(removed) + overlaps == 499
    assert sum(prime(n) for n in range(2, 3038)) == 435
    print("Every interval of 1501 odd candidates has at most 499 prime sums.")


if __name__ == "__main__":
    linear_bound()
    assert greedy(1, 15) == [1, 8, 7, 2, 13, 12, 3, 6, 9, 16, 5, 4, 11, 10, 15]
    terms = greedy(2, 11920)
    assert terms[:15] == [1, 8, 9, 2, 11, 10, 5, 12, 3, 4, 7, 6, 13, 14, 17]
    first = next((n, a) for n, a in enumerate(terms, 1) if abs(a - n) > 6)
    assert first == (11917, 11925)
    print("First absolute displacement above six:", first)
    print("Positions 11914 through 11920:", terms[11913:11920])
