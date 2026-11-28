"""Compare removal on a circle, the survivor recurrence, and the ceiling orbit."""
from bisect import bisect_right
from fractions import Fraction


def literal_circle(k, n):
    people = list(range(1, n + 1))
    position = 0
    while len(people) > 1:
        position = (position + k - 1) % len(people)
        people.pop(position)
    return people[0]


def populations(k, limit):
    b = k - 1
    orbit = [1]
    low = {}
    while orbit[-1] <= k * limit:
        d = orbit[-1]
        n = (d + b - 1) // b
        if k <= n <= limit:
            assert n not in low
            low[n] = 1 + b * n - d
        orbit.append(d + n)
    return orbit, low


def check_distribution(k, threshold):
    # Exact cumulative counts at the two extremal locations of a large orbit cell.
    b = k - 1
    lower = b * threshold / (k - threshold)
    d = 1
    successes = 0
    for i in range(801):
        left = (d + k - 1) // k
        right = (d + b - 1) // b - 1
        stop = min(right, (d - 1) * threshold.denominator //
                   (k * threshold.denominator - threshold.numerator))
        count = max(0, stop - left + 1)
        if i == 800:
            assert abs(Fraction(successes, left - 1) - lower) < Fraction(1, 10**12)
            assert abs(Fraction(successes + count, stop) - threshold) < Fraction(1, 10**12)
        successes += count
        d += (d + b - 1) // b


def main():
    limit = 100000
    circles = 0
    for k in range(2, 65):
        b = k - 1
        orbit, low = populations(k, limit)
        z = 0
        for n in range(1, limit + 1):
            z = (z + k) % n
            j = z + 1
            d = orbit[bisect_right(orbit, b * n)]
            assert b * n < d <= k * n and j == k * n + 1 - d
            if n >= k:
                assert (j <= b) == (n in low)
                if n in low:
                    assert low[n] == j
            if n <= 75:
                assert literal_circle(k, n) == j
                circles += 1
        term = 1
        partial = 0
        for d in orbit[:100]:
            partial += term
            assert partial == d
            term = (partial + b - 1) // b

    _, low5 = populations(5, 100)
    assert list(low5.items())[:7] == [(5,2),(6,1),(8,3),(10,3),(12,1),(15,1),(19,2)]
    trials = 0
    for k in range(2, 13):
        for x in (Fraction(1, 4), Fraction(1, 2), Fraction(3, 4)):
            check_distribution(k, x)
            trials += 1
    print(f"Matched the orbit formula and every low survivor for {63 * limit:,} step/population pairs.")
    print(f"Cross-checked {circles:,} of these by literal circular deletion.")
    print("Reproduced the k=5 opening populations and labels in OEIS A120160.")
    print(f"Compared both exact frequency endpoints in {trials} threshold tests at orbit index 800.")


if __name__ == "__main__":
    main()
