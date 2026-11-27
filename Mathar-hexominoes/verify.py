"""Exact finite-state certificate for Mathar (2013), formulas (49) and (50)."""

from collections import Counter


def columns(height, old):
    # The dictionary gives the mandatory band at each continued band's first row.
    fixed = {}
    row = 0
    for size, remaining in old:
        if remaining > 1:
            fixed[row] = (size, remaining - 1)
        row += size

    def fill(row):
        if row == height:
            yield ()
            return
        if row in fixed:
            choices = [fixed[row]]
        else:
            choices = [(size, 6 // size) for size in (2, 3)
                       if row + size <= height
                       and not any(row < start < row + size for start in fixed)]
        for size, remaining in choices:
            for rest in fill(row + size):
                yield ((size, remaining),) + rest

    return fill(0)


def meetings(old, new):
    new_breaks = set()
    row = 0
    for size, remaining in new[:-1]:
        row += size
        new_breaks.add(row)
    hits = 0
    row = 0
    for (size, above), (_, below) in zip(old, old[1:]):
        row += size
        hits += row in new_breaks and above == below == 1
    return hits


def graph(height, tatami):
    states = [()]
    index = {(): 0}
    edges = []
    for old in states:
        successors = []
        for new in columns(height, old):
            if tatami and meetings(old, new):
                continue
            if new not in index:
                index[new] = len(states)
                states.append(new)
            successors.append(index[new])
        edges.append(successors)
    accepting = [i for i, state in enumerate(states)
                 if all(remaining == 1 for size, remaining in state)]
    return edges, accepting


def certify(tatami, numerator, denominator):
    edges, accepting = graph(8, tatami)
    dimension = len(edges)
    start = max(max(denominator), max(numerator) + 1)
    counts = Counter({0: 1})
    coefficients = []
    for n in range(start + dimension):
        coefficients.append(sum(counts[i] for i in accepting))
        residual = sum(c * coefficients[n - i] for i, c in denominator.items()
                       if i <= n) - numerator.get(n, 0)
        if residual:
            raise AssertionError((n, residual, coefficients))
        following = Counter()
        for source, count in counts.items():
            for target in edges[source]:
                following[target] += count
        counts = following
    kind = "tatami" if tatami else "all"
    print(f"{kind}: {dimension} states, {sum(map(len, edges))} edges, "
          f"zero residual for widths 0 through {len(coefficients) - 1}")


if __name__ == "__main__":
    certify(False, {0: 1, 3: -2, 6: 1}, {0: 1, 3: -3, 9: 1, 12: -1})
    certify(True, {0: 1, 3: 2, 6: 3, 9: 4, 12: 5, 15: 4, 18: 3},
            {0: 1, 3: 1, 6: 1, 12: -1, 15: -1, 18: -1})
