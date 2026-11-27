"""Exact certificate for the two Gray recurrences with arbitrary positive seeds."""

from collections import Counter
from fractions import Fraction
from math import gcd


def gray(x):
    return x ^ (x >> 1)


def inverse_gray(x):
    result = x
    while x:
        x >>= 1
        result ^= x
    return result


def successors(u, v):
    total = u + 2 * v
    for h in range(total // 4, (total + 2) // 4 + 1):
        yield v, gray(h)


def lift(states):
    children = {(2*u + i, 2*v + j) for u, v in states
                for i in (0, 1) for j in (0, 1)}
    return {state: [w for w in successors(*state) if w in children]
            for state in children}


def cyclic_components(graph):
    # Kosaraju's algorithm. A singleton is cyclic exactly when it has a loop.
    reverse = {u: [] for u in graph}
    for u, edges in graph.items():
        for v in edges:
            reverse[v].append(u)
    seen = set()
    order = []
    for u in graph:
        if u in seen:
            continue
        stack = [(u, False)]
        while stack:
            x, finished = stack.pop()
            if finished:
                order.append(x)
            elif x not in seen:
                seen.add(x)
                stack.append((x, True))
                stack.extend((v, False) for v in graph[x])
    seen.clear()
    components = []
    for u in reversed(order):
        if u in seen:
            continue
        queue = [u]
        seen.add(u)
        for x in queue:
            for v in reverse[x]:
                if v not in seen:
                    seen.add(v)
                    queue.append(v)
        if len(queue) > 1 or u in graph[u]:
            components.append(set(queue))
    return components


def depths_and_period(component, graph):
    start = min(component)
    queue = [start]
    depth = {start: 0}
    period = 0
    for u in queue:
        for v in graph[u]:
            if v not in component:
                continue
            if v in depth:
                period = gcd(period, depth[u] + 1 - depth[v])
            else:
                depth[v] = depth[u] + 1
                queue.append(v)
    return depth, period


def bounds(u, v):
    return Fraction(2*v, u+1), Fraction(2*(v+1), u)


def analyze(component_depths, coordinate):
    records = []
    signs = [set() for _ in range(5)]
    for (u, v), d in component_depths.items():
        lower, upper = bounds(coordinate(u), coordinate(v))
        phase = d % 5
        assert upper < 2 or lower > 2
        signs[phase].add('+' if lower > 2 else '-')
        records.append((lower, upper, phase))
    assert all(len(letters) == 1 for letters in signs)
    word = ''.join(next(iter(letters)) for letters in signs)
    necklace = min(word[i:] + word[:i] for i in range(5))
    last_upper = [None] * 5
    gap = None
    for lower, upper, phase in sorted(records):
        for j, endpoint in enumerate(last_upper):
            if j != phase and endpoint is not None:
                difference = lower - endpoint
                gap = difference if gap is None else min(gap, difference)
        old = last_upper[phase]
        last_upper[phase] = upper if old is None else max(upper, old)
    assert gap is not None and gap > 0
    return necklace, gap


def seed_example(first, second):
    # These are seeds for b. Its conjugate a has seeds G(first), G(second).
    x, y = gray(first), gray(second)
    for _ in range(2, 101):
        x, y = y, gray(x + y)
    start = x >> (x.bit_length()-23), y >> (y.bit_length()-23)
    queue = [start]
    phase = {start: 101 % 5}
    signs = [set() for _ in range(5)]
    for u, v in queue:
        j = phase[u, v]
        l, h = bounds(inverse_gray(u), inverse_gray(v))
        assert l > 2 or h < 2
        signs[j].add('+' if l > 2 else '-')
        for w in successors(u, v):
            if w in phase:
                assert phase[w] == (j+1) % 5
            else:
                phase[w] = (j+1) % 5
                queue.append(w)
    assert all(len(row) == 1 for row in signs)
    return len(queue), ''.join(next(iter(row)) for row in signs)


def main():
    states = {(3, 3)}
    for bits in range(3, 24):
        graph = lift(states)
        components = cyclic_components(graph)
        states = set.union(*components)
    assert len(states) == 677 and len(components) == 15
    periods = Counter()
    words = [Counter(), Counter()]
    gaps = [Fraction(1), Fraction(1)]
    for component in components:
        depth, period = depths_and_period(component, graph)
        assert period % 5 == 0
        periods[period] += 1
        for i, coordinate in enumerate((lambda x: x, inverse_gray)):
            word, gap = analyze(depth, coordinate)
            words[i][word] += 1
            gaps[i] = min(gaps[i], gap)
    assert periods == {5: 11, 10: 4}
    assert words == [{'+-+--': 15}, {'+----': 12, '++-+-': 3}]
    assert gaps[0] > Fraction(86, 100000) and gaps[1] > Fraction(31, 100000)
    assert seed_example(1, 1) == (45, '+-+-+')
    assert seed_example(2, 1) == (67, '--+--')
    print('677 recurrent prefix pairs at 23 bits. 11 components of period 5 and 4 of period 10.')
    print('Signs up to cyclic shift: a +-+-- (all 15), b +---- (12) or ++-+- (3).')
    print('Smallest gaps between distinct phase sets:', *gaps)
    print('Both b sign patterns certified for seeds (1,1) and (2,1).')


if __name__ == '__main__':
    main()
