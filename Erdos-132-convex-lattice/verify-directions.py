"""Check the direction-count inequality for every subset of a 4-by-4 grid."""

from collections import Counter, defaultdict
from itertools import combinations, product


def check(points):
    multiplicity = Counter()
    directions = defaultdict(set)
    for (x, y), (u, v) in combinations(points, 2):
        dx, dy = u - x, v - y
        squared = dx * dx + dy * dy
        multiplicity[squared] += 1
        # The input is in lexicographic order, so the direction is canonical.
        directions[squared].add((dx, dy))

    larger = 0
    ranks = sorted(directions, reverse=True)
    for squared in ranks:
        count = len(directions[squared])
        assert multiplicity[squared] <= count * (1 + larger)
        larger += count

    bound = max(2, max(map(len, directions.values())))
    n = len(points)
    if bound <= n:
        length = 1 + (n - bound) // (bound * bound)
        assert length <= len(ranks)
        assert all(multiplicity[s] <= n for s in ranks[:length])


if __name__ == "__main__":
    grid = list(product(range(4), repeat=2))
    total = 0
    for size in range(2, len(grid) + 1):
        for subset in combinations(grid, size):
            check(subset)
            total += 1
    print(f"Verified the inequalities for {total:,} grid subsets.")
