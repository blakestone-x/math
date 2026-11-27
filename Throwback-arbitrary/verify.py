"""Exact orbit distributions and literal simulations of infinite throwback queues."""
from collections import Counter
from fractions import Fraction
from itertools import combinations, permutations, product
from math import gcd, prod


def physical_states(labels):
    for ranks in product(*(range(x - i + 1) for i, x in enumerate(labels))):
        placed = []
        for x, rank in zip(labels, ranks):
            free = [p for p in range(x + 1) if p not in placed]
            placed.append(free[rank])
        yield tuple(placed)


def edge(labels, positions):
    """All untracked heads cross every tracked position in a legal state."""
    head = labels[positions.index(0)] if 0 in positions else labels[-1] + 1
    return tuple(head if p == 0 else p - (p <= head) for p in positions)


def cycles(labels):
    unseen = set(physical_states(labels))
    while unseen:
        start = min(unseen)
        path = []
        state = start
        while state in unseen:
            unseen.remove(state)
            path.append(state)
            state = edge(labels, state)
        assert state == start
        yield path


def forecast(x, positions, lower_orbit):
    """Apply the congruence formula at the given starting phase of the base orbit."""
    r = x - len(positions) + 2
    rank = positions[-1] - sum(p < positions[-1] for p in positions[:-1])
    active = sum(0 not in state for state in lower_orbit)
    g = gcd(r, active)
    visits = [0] * (x + 1)
    elapsed = 0
    for state in lower_orbit:
        free = [p for p in range(x + 1) if p not in state]
        for v in free[(rank - elapsed) % g::g]:
            visits[v] += 1
        elapsed += 0 not in state
    return visits, len(lower_orbit) * (r // g), active // g * (r - 1)


def exhaustive(max_label=7):
    lookup = {(): {(): ((),)}}
    sets = orbits = states = 0
    for k in range(1, max_label + 1):
        for labels in combinations(range(1, max_label + 1), k):
            sets += 1
            x = labels[-1]
            lower = lookup[labels[:-1]]
            lookup[labels] = {}
            lengths = set()
            num_orbits = 0
            for orbit in cycles(labels):
                num_orbits += 1
                actual = Counter(state[-1] for state in orbit)
                pass_count = sum(0 not in state for state in orbit)
                actual_counts = [actual[p] for p in range(x + 1)]
                lengths.add(len(orbit))
                for i, state in enumerate(orbit):
                    pred, period, passes = forecast(x, state, lower[state[:-1]])
                    assert (pred, period, passes) == (actual_counts, len(orbit), pass_count)
                    # The largest sets need no base orbit for a further extension.
                    if x < max_label:
                        lookup[labels][state] = tuple(orbit[i:] + orbit[:i])
                orbits += 1
                states += len(orbit)
            capacity = prod(v - i + 1 for i, v in enumerate(labels))
            assert lengths == {capacity // num_orbits} and capacity % num_orbits == 0
    print(f"All {sets} nonempty label sets in 1..{max_label}: {orbits} orbits, {states} starting states.")


def literal_word(front, steps):
    queue = list(front)
    next_label = len(front) + 1
    stream = []
    for _ in range(steps):
        d = queue[0]
        needed = max(0, d + 1 - len(queue))
        queue.extend(range(next_label, next_label + needed))
        next_label += needed
        queue.pop(0)
        queue.insert(d, d)
        stream.append(d)
    return stream


def literal_tests():
    legal = witnesses = 0
    for front in permutations(range(1, 7)):
        u = literal_word(front, 256)
        bad = [x for i, x in enumerate(front) if i > x]
        if not bad:
            legal += 1
            # Six consecutive smallest labels have period 2^6.
            capped = [min(x, 7) for x in u]
            assert capped[:-64] == capped[64:]
        for x in bad:
            length = u.index(x) + 1
            word = u[:length]
            assert all(u[s:s + length] != word for s in range(1, len(u) - length + 1))
            witnesses += 1
    print(f"720 permuted queues, 256 literal steps each: {legal} legal starts and {witnesses} unique-prefix checks.")
    for initial, expected in [((0, 1), Fraction(13, 6)), ((0, 2), Fraction(7, 3))]:
        p = initial
        orbit = []
        while p not in orbit:
            orbit.append(p)
            p = edge((2, 4), p)
        assert p == initial and Fraction(sum(s[1] for s in orbit), len(orbit)) == expected
    print("Exact means of label 4 in the two six-step orbits: 13/6 and 7/3.")


if __name__ == "__main__":
    exhaustive()
    literal_tests()
