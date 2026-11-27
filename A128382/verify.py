"""Compute tau from its defining product and verify zeros by divisor summation."""
from math import comb


def tau_prefix(n):
    values = [0, 1] + [0] * (n - 1)
    for part in range(1, n):
        for index in range(n, part, -1):
            terms = min(24, (index - 1) // part)
            values[index] += sum((-1)**j * comb(24, j) * values[index - j * part]
                                 for j in range(1, terms + 1))
    return values


def divisor_sum(values):
    sums = [0] * len(values)
    for d in range(1, len(values)):
        for n in range(d, len(values), d):
            sums[n] += values[d]
    return sums


if __name__ == "__main__":
    values = tau_prefix(100)
    assert values[1:8] == [1, -24, 252, -1472, 4830, -6048, -16744]
    short = values[:8]
    for _ in range(16744):
        short = divisor_sum(short)
    assert short[7] == 0
    for _ in range(24):
        values = divisor_sum(values)
    assert values[1:9] == [1, 0, 276, -1748, 4854, 0, -16720, 44552]
    assert all(values[n] == 0 for n in range(2, len(values), 4))
    print("All 16,744 divisor sums at index 7 checked; the 24th iterate matches A128382.")
