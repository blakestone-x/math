"""Compare exact divisor counts with direct folds and direct four-corner tests."""
from itertools import combinations
from math import comb


def triangular(n):
    return n * (n + 1) // 2


def factor(n):
    factors = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            factors[p] = factors.get(p, 0) + 1
            n //= p
        p = 3 if p == 2 else p + 2
    if n > 1:
        factors[n] = 1
    return factors


def divisor_folds(n):
    factors = {}
    for x in (n, n + 1):
        for p, e in factor(x).items():
            factors[p] = factors.get(p, 0) + e
    factors[2] -= 1
    divisors = [1]
    for p, e in factors.items():
        divisors = [d * p ** i for d in divisors for i in range(e + 1)]
    perimeter = triangular(n)
    return {(a, b) for a in divisors
            if a < (b := perimeter // a) and (a + b) % 2 == 1
            and a + b <= 2 * n - 1}


def direct_folds(n):
    perimeter = triangular(n)
    return sum(2 * (triangular(j) - triangular(i)) == perimeter
               for i, j in combinations(range(n), 2))


def direct_rectangles(n):
    marks = [triangular(i) for i in range(n)]
    perimeter = triangular(n)
    return sum(b - a == d - c and c - b == perimeter + a - d
               for a, b, c, d in combinations(marks, 4))


def main():
    for n in range(1, 251):
        count = len(divisor_folds(n))
        assert count == direct_folds(n)
        if n <= 40:
            assert comb(count, 2) == direct_rectangles(n)
    print("Fold counts agree for n=1..250; rectangle counts agree for n=1..40.")

    # Both admissible residue classes, with one, two, and three folds.
    examples = ((64, 1), (415, 1), (322816, 2), (89023, 2),
                (492398848, 3), (208964863, 3))
    for n, k in examples:
        pairs = sorted(divisor_folds(n))
        assert len(pairs) == k
        print(f"n={n}: {k} folds, factors {pairs}")


if __name__ == "__main__":
    main()
