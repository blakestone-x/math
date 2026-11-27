"""Check the fixed-minimum decomposition against explicit compositions and OEIS."""

from collections import Counter
from math import comb


def by_compositions(n):
    row = Counter()
    def visit(left, smallest, frequency):
        if left == 0:
            row[frequency] += 1
            return
        for part in range(1, left + 1):
            if part < smallest:
                visit(left - part, part, 1)
            else:
                visit(left - part, smallest, frequency + (part == smallest))
    visit(n, n + 1, 0)
    return [row[k] for k in range(n + 1)]


def by_minimum(n):
    row = [0] * (n + 1)
    if n == 0:
        return [1]
    # With m the minimum and j other parts, distribute the excess weight
    # among these j ordered parts, then insert the k copies of m.
    for m in range(1, n + 1):
        for k in range(1, n // m + 1):
            rest = n - k*m
            row[k] += (rest == 0)
            for j in range(1, rest // (m + 1) + 1):
                extra = rest - (m + 1)*j
                row[k] += comb(extra + j - 1, j - 1) * comb(j + k, k)
    return row


if __name__ == "__main__":
    for n in range(19):
        assert by_compositions(n) == by_minimum(n)
    assert by_minimum(15) == [0, 1352, 2283, 2872, 2925, 2512, 1862, 1238,
                              684, 395, 143, 90, 13, 14, 0, 1]
    for n in range(1, 71):
        assert sum(by_minimum(n)) == 2**(n - 1)
    print("Verified complete composition enumerations through 18, the published row 15,")
    print("and all row sums through 70.")
