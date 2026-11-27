"""Exhaustive finite checks of Lemma 1. Run with Python 3."""

from collections import Counter, defaultdict
from itertools import product


def check_partition(points, labels):
    """Labels 1 and 2 are the two parts. Label 0 omits a grid point."""
    chosen = [(p, part) for p, part in zip(points, labels) if part]
    n = len(chosen)
    if n < 2:
        return False
    directions = defaultdict(lambda: defaultdict(set))
    edges = defaultdict(Counter)
    unordered = Counter()
    pinned = defaultdict(Counter)
    for i, ((x, y), source) in enumerate(chosen):
        for j, ((xx, yy), target) in enumerate(chosen):
            if i == j:
                continue
            v = xx - x, yy - y
            s = v[0] ** 2 + v[1] ** 2
            pair = source, target
            directions[pair][s].add(v)
            edges[pair][s] += 1
            pinned[i][s] += 1
            if i < j:
                unordered[s] += 1

    lengths = sorted(unordered, reverse=True)
    shell_bound = max(len(vectors) for pair in directions.values()
                      for vectors in pair.values())
    parts = len({part for _, part in chosen})
    for pair, layers in directions.items():
        longer = 0
        for s in lengths:
            count = len(layers.get(s, ()))
            assert edges[pair][s] <= count * (1 + longer)
            longer += count
    assert all(count <= parts * shell_bound
               for histogram in pinned.values() for count in histogram.values())
    guaranteed = (n - 1) // (parts ** 2 * shell_bound ** 2)
    assert len(lengths) >= guaranteed
    assert all(unordered[s] <= n for s in lengths[:guaranteed])
    return True


def main():
    grid = tuple(product(range(3), repeat=2))
    checked = sum(check_partition(grid, labels)
                  for labels in product(range(3), repeat=len(grid)))
    assert checked == 3 ** 9 - 1 - 2 * 9
    print(f"Verified all {checked:,} labeled grid subsets with at least two points.")
    # Powers of two have unique positive differences. Including both orientations gives U=2.
    powers = [(2 ** i, 0) for i in range(10)]
    assert check_partition(powers, [1] * len(powers))
    print("Verified a ten-point example with a positive guaranteed prefix.")


if __name__ == "__main__":
    main()
