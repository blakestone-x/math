"""Alternating universal Gray recurrence. Standard-library finite prefix proof."""

from collections import Counter
from fractions import Fraction


def inverse_gray(n):
    value = n
    while n:
        n >>= 1
        value ^= n
    return value


def gray(n):
    return n ^ (n >> 1)


def successors(state, width, direct=False):
    u, v = state
    total = gray(u) + gray(v) if direct else u + v
    for h in (total, total+1):
        increase = int(h >= 1 << width)
        image = gray(h) if direct else h ^ (h >> 2)
        yield (v >> increase, image >> increase), increase


def recurrent(graph):
    reverse = {u: [] for u in graph}
    for u, out in graph.items():
        for v, _ in out:
            reverse[v].append(u)
    seen = set()
    order = []
    for u in graph:
        if u in seen:
            continue
        walk = [(u, False)]
        while walk:
            x, exiting = walk.pop()
            if exiting:
                order.append(x)
            elif x not in seen:
                seen.add(x)
                walk.append((x, True))
                walk.extend((v, False) for v, _ in graph[x])
    seen.clear()
    groups = []
    for u in reversed(order):
        if u in seen:
            continue
        queue = [u]
        seen.add(u)
        for v in queue:
            for w in reverse[v]:
                if w not in seen:
                    seen.add(w)
                    queue.append(w)
        if len(queue) > 1 or any(v == u for v, _ in graph[u]):
            groups.append(set(queue))
    return groups


def four_ratios(states, graph, direct):
    vertices = sorted(states)
    ids = {q: k for k, q in enumerate(vertices)}
    next_two = []
    ratio = []
    scale = 1 << 19
    for u, v in vertices:
        children = {w for w, _ in graph[u, v] if w in states}
        grandchildren = {ids[z] for w in children for z, _ in graph[w] if z in states}
        next_two.append(sorted(grandchildren))
        x, y = (u, v) if direct else (inverse_gray(u), inverse_gray(v))
        ratio.append((scale*y // (x+1), (scale*(y+1)+x-1) // x))

    visits = 0
    def check(k, depth, selected):
        nonlocal visits
        visits += 1
        lo, hi = ratio[k]
        if all(lo > h+128 or l > hi+128 for l, h in selected):
            selected = selected + ((lo, hi),)
        if len(selected) == 3:
            return
        assert depth < 4, 'A four-ratio path has fewer than three separated enclosures.'
        for child in next_two[k]:
            check(child, depth+1, selected)

    for k in range(len(vertices)):
        check(k, 1, ())
    assert visits == 1209839
    print(f'{visits:,} partial paths checked for the four-ratio bound.')


def run(direct=False):
    states = {(u, v) for u in range(1, 4) for v in range(2, 4)}
    for s in range(2, 20):
        if s > 2:
            states = {(2*u+i, 2*v+j) for u, v in states for i in (0, 1) for j in (0, 1)}
        graph = {q: [(w, e) for w, e in successors(q, s, direct) if w in states] for q in states}
        groups = recurrent(graph)
        states = set.union(*groups)
        if s in (2, 6, 12, 16, 17, 18, 19):
            print(f'{s} bits: {len(states)} recurrent vertices in {len(groups)} components.')
    assert len(states) == 99771 and len(groups) == 1
    intervals = {0: [], 1: []}
    counts = Counter()
    for u, v in states:
        incoming = int(u < 1 << 18)
        # The preceding value has smaller length precisely for an incoming rise.
        for w, outgoing in graph[u, v]:
            if w in states:
                assert incoming + outgoing == 1
                counts[incoming] += 1
        x, y = (u, v) if direct else (inverse_gray(u), inverse_gray(v))
        intervals[incoming].append((Fraction(y, x+1), Fraction(y+1, x)))
    expected = [(60914, Fraction(23384,42965), Fraction(327170,516613)),
                (38857, Fraction(516677,163824), Fraction(261182,70185))]
    for k in (0, 1):
        lo = min(l for l, h in intervals[k])
        hi = max(h for l, h in intervals[k])
        assert (len(intervals[k]),lo,hi) == expected[k]
        print(f'Incoming rise {k}: {len(intervals[k])} pairs, {counts[k]} edge entries, '
              f'ratio lower {lo}, upper {hi}.')
    four_ratios(states, graph, direct)
    return states


if __name__ == '__main__':
    conjugate = run(False)
    direct = run(True)
    assert {(gray(u), gray(v)) for u, v in direct} == conjugate
    print('The two coordinate systems agree on every retained pair.')
