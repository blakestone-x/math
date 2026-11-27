"""Compare exact covers with the four-junction block formula. Standard Python."""

from collections import Counter
from math import comb


def cell_counts(k, height, width):
    """Place bars at the first empty cell and inspect each completed board."""
    grid = [-1] * (height * width)
    counts = Counter()

    def visit(tile):
        try:
            p = grid.index(-1)
        except ValueError:
            junctions = 0
            for r in range(height - 1):
                for c in range(width - 1):
                    i = r * width + c
                    corners = (grid[i], grid[i+1], grid[i+width], grid[i+width+1])
                    junctions += len(set(corners)) == 4
            counts[junctions] += 1
            return
        r, c = divmod(p, width)
        for stride, fits in ((1, c+k <= width), (width, r+k <= height)):
            if fits:
                cells = range(p, p + k * stride, stride)
                if all(grid[i] == -1 for i in cells):
                    for i in cells:
                        grid[i] = tile
                    visit(tile + 1)
                    for i in cells:
                        grid[i] = -1

    visit(0)
    return counts


def block_counts(k, height, max_units):
    """Multiply block weights and interface weights through the given width."""
    t = height-k
    # Integer -1 denotes U. The other types are their upper exterior row counts.
    blocks = [(-1, 1, 0, 1)]
    for s in range(t+1):
        blocks.append((s, 1, 0, 1))
        exterior = max(s-1, 0) + max(t-s-1, 0)
        for j in range(1, max_units):
            for used in range(1, min(k-1, j)+1):
                multiplicity = comb(k-1, used) * comb(j-1, used-1)
                junctions = j * exterior + (j-used) * (k-1)
                blocks.append((s, 1+j, junctions, multiplicity))

    def cut(left, right):
        if left is None:
            return 0
        if left == right == -1:
            return height-1
        if -1 in (left, right):
            return t
        return t-abs(left-right)

    paths = [Counter() for _ in range(max_units+1)]
    paths[0][None, 0] = 1
    for units, layer in enumerate(paths):
        for (last, previous), amount in layer.items():
            for s, length, internal, choices in blocks:
                if units+length <= max_units:
                    junctions = previous + internal + cut(last, s)
                    paths[units+length][s, junctions] += amount * choices
    totals = []
    for layer in paths:
        counts = Counter()
        for (_, j), amount in layer.items():
            counts[j] += amount
        totals.append(counts)
    return totals


def zero_counts(k, height, limit):
    t = height-k
    if t == 1:
        series = [1]
        for n in range(1, limit+1):
            series.append(sum(comb(k-1, i-1)*series[n-i]
                              for i in range(1, min(n, k)+1)))
        return [1] + [2*series[n] + (n == 1) for n in range(1, limit+1)]
    return [1, t+2] + [2 + (comb(k-1, n-1) if t == 2 and n <= k else 0)
                       for n in range(2, limit+1)]


if __name__ == "__main__":
    boards = 0
    for k in range(2, 7):
        for height in range(k+1, 2*k):
            limit = 4 if k <= 4 else 3
            by_blocks = block_counts(k, height, limit)
            by_zero_formula = zero_counts(k, height, limit)
            for width in range(k*limit+1):
                actual = cell_counts(k, height, width)
                expected = by_blocks[width//k] if width % k == 0 else Counter()
                if actual != expected:
                    raise AssertionError((k, height, width, actual, expected))
                if width % k == 0 and actual[0] != by_zero_formula[width//k]:
                    raise AssertionError(("tatami", k, height, width))
                boards += 1
    print(f"Verified every junction count on {boards} boards (bar lengths 2–6).")
