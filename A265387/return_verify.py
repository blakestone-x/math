"""Lag-140 certificate. Add --cross-check to repeat in the conjugate coordinates."""

import argparse
from collections import deque
from universal_verify import gray, inverse_gray

PERIOD = 140
START = 24000
FIRST_BITS = 132


def next_pairs(pair, conjugate):
    u, v = pair
    total = gray(u) + 2*gray(v) if conjugate else u + 2*v
    for h in range(total // 4, (total + 2) // 4 + 1):
        yield (v, h) if conjugate else (v, gray(h))


def seed(conjugate):
    x, y = 1, 1
    for _ in range(2, START+1):
        term = gray(x) + gray(y) if conjugate else gray(x+y)
        x, y = y, term
    return x >> (START-FIRST_BITS), y >> (START+1-FIRST_BITS)


def initial_graph(conjugate):
    first = seed(conjugate)
    vertices = [first]
    phase = [START % PERIOD]
    ids = {first: 0}
    edges = []
    for j, pair in enumerate(vertices):
        dest = []
        for nxt in next_pairs(pair, conjugate):
            k = ids.get(nxt)
            if k is None:
                k = len(vertices)
                ids[nxt] = k
                vertices.append(nxt)
                phase.append((phase[j]+1) % PERIOD)
            else:
                assert phase[k] == (phase[j]+1) % PERIOD
            dest.append(k)
        edges.append(dest)
    return vertices, phase, edges


def ratio_gap(vertices, phase, coordinate):
    scale = 1 << 133
    bands = [None] * PERIOD
    for (u, v), j in zip(vertices, phase):
        u, v = coordinate(u), coordinate(v)
        l = 2*scale*v // (u+1)
        h = (2*scale*(v+1) + u-1) // u
        old = bands[j]
        bands[j] = (l, h) if old is None else (min(l, old[0]), max(h, old[1]))
    ordered = sorted(bands)
    return min(r[0]-l[1] for l, r in zip(ordered, ordered[1:]))


def paths_from(starts, rows, edges):
    """Forward source labels along exactly one block, with a separate final layer."""
    forward = [0] * len(edges)
    for i, k in enumerate(starts):
        forward[k] = 1 << i
    final = {}
    for j, layer in enumerate(rows):
        for k in layer:
            mask = forward[k]
            if not mask:
                continue
            for v in edges[k]:
                if j == PERIOD-1:
                    final[v] = final.get(v, 0) | mask
                else:
                    forward[v] |= mask
    return forward, final


def keep_near_returns(vertices, phase, edges, conjugate):
    rows = [[] for _ in range(PERIOD)]
    for k, j in enumerate(phase):
        rows[j].append(k)
    # Endpoint comparison always uses the a coordinates. G maps b prefixes to a.
    coordinate = gray if conjugate else lambda x: x
    positions = {tuple(map(coordinate, vertices[k])): k for k in rows[0]}
    neighbors = {k: [positions[u+i, v+j] for i in (-1, 0, 1) for j in (-1, 0, 1)
                     if (u+i, v+j) in positions] for (u, v), k in positions.items()}
    _, final = paths_from(rows[0], rows, edges)
    start_id = {k: i for i, k in enumerate(rows[0])}
    valid_start = {k for w, mask in final.items() for k in neighbors[w]
                   if (mask >> start_id[k]) & 1}
    if not valid_start:
        return [], []
    # Repeat with only viable source labels to reduce bitset size.
    starts = sorted(valid_start)
    start_id = {k: i for i, k in enumerate(starts)}
    forward, final = paths_from(starts, rows, edges)
    backward = [0] * len(vertices)
    endpoints = set(valid_start)
    for w, reachable in final.items():
        allowed = sum(1 << start_id[k] for k in neighbors[w] if k in start_id)
        backward[w] = allowed
        if reachable & allowed:
            endpoints.add(w)
    for layer in reversed(rows[1:]):
        for k in layer:
            mask = 0
            for w in edges[k]:
                mask |= backward[w]
            backward[k] = mask
    keep = [k for k, j in enumerate(phase)
            if (j == 0 and k in endpoints) or (j != 0 and forward[k] & backward[k])]
    return [vertices[k] for k in keep], [phase[k] for k in keep]


def lift(vertices, phase, conjugate):
    children = [(2*u+i, 2*v+j) for u, v in vertices for i in (0, 1) for j in (0, 1)]
    ids = {pair: i for i, pair in enumerate(children)}
    edges = [[ids[w] for w in next_pairs(pair, conjugate) if w in ids] for pair in children]
    return children, [j for j in phase for _ in range(4)], edges


def run(conjugate):
    vertices, phase, edges = initial_graph(conjugate)
    assert len(vertices) == 126281
    gaps = tuple(ratio_gap(vertices, phase, f) for f in
                 ((gray, lambda x: x) if conjugate else (lambda x: x, inverse_gray)))
    assert gaps == (1498900861973, 2852760788761)
    name = 'b' if conjugate else 'a'
    print(f'{name} coordinates: 126,281 states, least ratio gaps {gaps} in units of 2^-133.',
          flush=True)
    checkpoints = {132: 39524, 180: 7668, 181: 3421, 182: 2114, 183: 990, 184: 0}
    counts = []
    for bits in range(FIRST_BITS, 185):
        vertices, phase = keep_near_returns(vertices, phase, edges, conjugate)
        counts.append(len(vertices))
        if bits in checkpoints:
            assert len(vertices) == checkpoints[bits]
            print(f'{bits} bits: {len(vertices):,} distinct possible path vertices.', flush=True)
        if not vertices:
            assert bits == 184
            break
        vertices, phase, edges = lift(vertices, phase, conjugate)
    return counts


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cross-check', action='store_true')
    args = parser.parse_args()
    counts = run(False)
    if args.cross_check:
        assert run(True) == counts
        print('Both coordinate systems agree at all 53 precisions.')
