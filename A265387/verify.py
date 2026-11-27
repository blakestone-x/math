"""Exact prefix induction for A265385 and A265387. Standard-library Python 3.9+."""
from collections import deque
from csv import DictReader
from pathlib import Path


def gray(value):
    return value ^ (value >> 1)


def a_seed(bits):
    x, y = 1, 1
    for _ in range(2, bits + 1):
        x, y = y, gray(x + y)
    return x, y // 2


def b_seed(bits):
    x, y = 1, 1
    for _ in range(2, bits + 1):
        x, y = y, gray(x) + gray(y)
    return x, y // 2


def a_successors(u, v):
    total = u + 2 * v
    for h in range(total // 4, (total + 2) // 4 + 1):
        yield v, gray(h)


def b_successors(u, v):
    total = gray(u) + 2 * gray(v)
    return {(v, (total + carry) // 4) for carry in (0, 1, 2)}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def phase_graph(bits, period, seed, successors, depth_first=False):
    first = seed(bits)
    residues = {first: (bits + 1) % period}  # numerator index for each pair
    queue = deque([first])
    edges = 0
    while queue:
        u, v = queue.pop() if depth_first else queue.popleft()
        next_phase = (residues[u, v] + 1) % period
        for pair in successors(u, v):
            edges += 1
            if pair not in residues:
                residues[pair] = next_phase
                queue.append(pair)
            else:
                require(residues[pair] == next_phase, "inconsistent phase")
    return residues, edges


def bands(residues, period, scale):
    table = [None] * period
    for (u, v), phase in residues.items():
        require(u > 0 and v > 0, "nonpositive prefix")
        lower = (2 * scale * v) // (u + 1)
        upper = (2 * scale * (v + 1) + u - 1) // u
        old = table[phase]
        table[phase] = (lower, upper) if old is None else (
            min(lower, old[0]), max(upper, old[1])
        )
    require(all(row is not None for row in table), "missing phase")
    return table


def gap(table):
    ordered = sorted(table)
    return min(right[0] - left[1] for left, right in zip(ordered, ordered[1:]))


def check(bits, period, scale, expected):
    a_states, a_edges = phase_graph(bits, period, a_seed, a_successors)
    b_states, b_edges = phase_graph(bits, period, b_seed, b_successors, depth_first=True)
    require(len(a_states) == len(b_states) == expected, "state count")
    require(a_edges == b_edges, "edge count")
    require(all(a_states.get((gray(u), gray(v))) == phase
                for (u, v), phase in b_states.items()), "conjugacy of phase graphs")
    a_bands = bands(a_states, period, scale)
    b_bands = bands(b_states, period, scale)
    require(gap(a_bands) > 0 and gap(b_bands) > 0, "intervals overlap")
    print(f"{bits}-bit precision, period {period}: {expected:,} states and "
          f"{a_edges:,} distinct directed transitions in each graph.")
    print(f"Smallest gap in units of 1/{scale}: A265385 {gap(a_bands)}, "
          f"A265387 {gap(b_bands)}.")
    return a_bands, b_bands


def main():
    coarse_a, coarse_b = check(19, 5, 10_000, 13)
    require(coarse_a == [(19841, 19842), (20220, 20221), (19752, 19753),
                         (20202, 20204), (19986, 19987)], "five-phase A table")
    require(coarse_b == [(20058, 20059), (19889, 19890), (20093, 20094),
                         (19907, 19908), (20051, 20052)], "five-phase B table")
    fine = check(96, 35, 10**12, 316_710)
    with Path(__file__).with_name("intervals.csv").open() as data:
        rows = list(DictReader(data))
    require(len(rows) == 35, "CSV length")
    for i, row in enumerate(rows):
        require(int(row["n_mod_35"]) == i, "CSV phase")
        for bounds, prefix in zip(fine, ("A265385", "A265387")):
            require(bounds[i] == (int(row[prefix + "_lower"]), int(row[prefix + "_upper"])),
                    f"CSV row {i} for {prefix}")
    print("Both inductions reproduce every published interval.")


if __name__ == "__main__":
    main()
