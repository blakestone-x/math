"""Independent checks against absolute queue positions and literal throwback moves."""
from fractions import Fraction
from itertools import combinations
from math import gcd, prod


def arithmetic(labels):
    period, holes = 1, 1
    radices = []
    for index, label in enumerate(labels):
        radix = label - index + 1
        divisor = gcd(radix, holes)
        period *= radix // divisor
        holes = holes // divisor * (radix - 1)
        radices.append(radix)
    compatible = all(gcd(rj, ri - 1) == 1
                     for j, rj in enumerate(radices) for ri in radices[:j])
    return period, holes, prod(radices), compatible


def direct_cycle(labels):
    # All untracked labels exceed the tracked maximum. Whenever an untracked
    # label leads, it passes every tracked label regardless of its identity.
    initial = tuple(range(len(labels)))
    positions = initial
    seen = set()
    holes = 0
    position_totals = [0] * len(labels)
    while positions not in seen:
        seen.add(positions)
        position_totals = [a + b for a, b in zip(position_totals, positions)]
        if 0 in positions:
            jump = labels[positions.index(0)]
        else:
            holes += 1
            jump = labels[-1] + 1
        positions = tuple(jump if p == 0 else p - (p <= jump) for p in positions)
    assert positions == initial
    return len(seen), holes, position_totals


def literal_leaders(minimum, count):
    # Append untouched input labels just in time for the actual list insertion.
    queue = [minimum]
    fresh = minimum + 1
    for _ in range(count):
        leader = queue.pop(0)
        while len(queue) < leader:
            queue.append(fresh)
            fresh += 1
        queue.insert(leader, leader)
        yield leader


def select(m, k):
    return k + 1 + k // m


def occurrence(m, j, k):
    t = (m + 1) * k
    for _ in range(j):
        t = select(m, t)
    return t


def main():
    prefixes = 0
    for size in range(1, 10):
        for labels in combinations(range(1, 10), size):
            predicted, passes, capacity, compatible = arithmetic(labels)
            actual, free, totals = direct_cycle(labels)
            assert (predicted, passes) == (actual, free), labels
            assert (actual == capacity) == compatible, labels
            if compatible:
                means = []
                for i, x in enumerate(labels):
                    mean = (Fraction(x * (x + 1), 2) - sum(means)) / (x - i + 1)
                    assert mean == Fraction(totals[i], actual), (labels, i)
                    means.append(mean)
            prefixes += 1
    for m in range(1, 9):
        count = 12000
        by_label = {}
        for t, label in enumerate(literal_leaders(m, count)):
            j = label - m
            k = by_label.get(j, 0)
            assert t == occurrence(m, j, k), (m, j, k)
            by_label[j] = k + 1
        for j, k in by_label.items():
            assert occurrence(m, j, k) >= count
        for j in range(6):
            size = m ** j
            times = [occurrence(m, j, k) for k in range(size + 1)]
            gaps = [b - a for a, b in zip(times, times[1:])]
            assert sum(gaps) == (m + 1) ** (j + 1)
            assert gaps[:-1] == gaps[:-1][::-1]
            assert gaps[-1] == m + 1 + 2 * times[0]
    print(f"PASS: periods and free steps for {prefixes} increasing prefixes from 1..9")
    print("PASS: full-orbit mean positions for every compatible prefix in that set")
    print("PASS: 96,000 literal queue moves; exact occurrence indices and gap symmetries")


if __name__ == "__main__":
    main()
