"""Compare both integer equations, the run condition, and the counting corollary."""

from itertools import groupby


def carryless(u, n):
    result = 0
    while u:
        if u & 1:
            result ^= n
        u >>= 1
        n <<= 1
    return result


def run_test(n, d):
    if n == 0:
        return True
    word = format(n, "b").rstrip("0")
    return all(sum(1 for _ in group) >= d for _, group in groupby(word))


if __name__ == "__main__":
    width = 16
    for d in range(2, 11):
        counts = [0] * (width + 1)
        for n in range(1 << width):
            a = ((1 << d) - 1) * n == carryless((1 << d) + 3, n)
            b = ((1 << (d - 1)) + 1) * n == carryless((1 << d) + (1 << (d - 1)) + 1, n)
            if not (a == b == run_test(n, d)):
                raise AssertionError((d, n))
            if a and n:
                counts[n.bit_length()] += 1
        for length in range(1, width + 1):
            rhs = int(length == d) + 2 * counts[length - 1]
            if length >= 2:
                rhs -= counts[length - 2]
            if length >= 2 * d:
                rhs += counts[length - 2 * d]
            if rhs != counts[length]:
                raise AssertionError((d, length, rhs, counts[length]))
    print("Verified all n < 2^16 for 2 <= d <= 10, including the counting formula.")
