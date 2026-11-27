"""Compare the polygonal recurrence directly with every predicted plateau."""
from itertools import groupby


def column(k, limit):
    m = k + 2
    shifts = []
    j = 1
    while m * j * (j - 1) // 2 + j <= limit:
        for h in (j, -j):
            shifts.append((m * h * (h - 1) // 2 + h, 1 if j % 2 else -1))
        j += 1
    values = [1]
    for n in range(1, limit + 1):
        values.append(sum(sign * values[n - i] for i, sign in shifts if i <= n))
    return values


def levels(limit):
    p = [1] + [0] * limit
    for t in range(1, limit + 1):
        for color in range(3):
            for n in range(t, limit + 1):
                p[n] += p[n - t]
    return [sum(p[:r+1]) for r in range(limit + 1)]


if __name__ == "__main__":
    plateau_levels = levels(20)
    for k in range(1, 41):
        last = (k - 1) // 2
        limit = (last + 2) * (k + 3) + 10
        actual = []
        start = 0
        for value, run in groupby(column(k, limit)):
            length = sum(1 for _ in run)
            if length >= 2:
                actual.append((start, length, value))
            start += length
        expected = [(r*(k+3), k+1-2*r, plateau_levels[r]) for r in range(last+1)]
        assert actual == expected, (k, actual, expected)
    assert plateau_levels[:8] == [1, 4, 13, 35, 86, 194, 415, 844]
    print("All predicted plateau positions, lengths and levels checked for 40 columns.")
