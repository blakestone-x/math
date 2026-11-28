"""Check all 140 ratio progressions in both observables with a binary prefix graph."""

import argparse
from pathlib import Path
import struct
import subprocess
import tempfile

from return_verify import FIRST_BITS, PERIOD, initial_graph, lift, paths_from
from universal_verify import gray, inverse_gray


def endpoint_ranks(vertices, coordinate, bits):
    scale = 1 << bits
    intervals = []
    for u, v in vertices:
        x, y = coordinate(u), coordinate(v)
        lower = 2*scale*y // (x+1)
        upper = (2*scale*(y+1) + x-1) // x
        intervals.append((lower, upper))
    # Each sorted endpoint is assigned its exact order rank, preserving ties.
    endpoints = sorted({value for bounds in intervals for value in bounds})
    rank = {value: i for i, value in enumerate(endpoints)}
    return [(rank[l], rank[h]) for l, h in intervals]


def cyclic_paths(executable, vertices, phases, edges, bits, conjugate):
    a_coordinate = gray if conjugate else lambda x: x
    b_coordinate = (lambda x: x) if conjugate else inverse_gray
    a = endpoint_ranks(vertices, a_coordinate, bits)
    b = endpoint_ranks(vertices, b_coordinate, bits)
    record = struct.Struct('=7i')
    data = bytearray(struct.pack('=i', len(vertices)))
    for i, phase in enumerate(phases):
        dest = edges[i] + [-1, -1]
        data.extend(record.pack(phase, dest[0], dest[1],
                                a[i][0], b[i][0], a[i][1], b[i][1]))
    mask = subprocess.run([executable], input=data, stdout=subprocess.PIPE, check=True).stdout
    assert len(mask) == len(vertices) and set(mask) <= {0, 1}
    return ([v for v, selected in zip(vertices, mask) if selected],
            [r for r, selected in zip(phases, mask) if selected])


def verify_empty_return_graphs(vertices, phases, edges, bits, conjugate):
    """At the final precision, check all 280 graphs again in Python by vertex deletion."""
    rows = [[] for _ in range(PERIOD)]
    for k, j in enumerate(phases):
        rows[j].append(k)
    coordinates = (gray, lambda x: x) if conjugate else (lambda x: x, inverse_gray)
    observables = [endpoint_ranks(vertices, fn, bits) for fn in coordinates]
    for phase, starts in enumerate(rows):
        _, reachable = paths_from(starts, rows[phase:] + rows[:phase], edges)
        for intervals in observables:
            adjacency = [[] for _ in starts]
            indegree = [0] * len(starts)
            for j, target in enumerate(starts):
                lower, upper = intervals[target]
                mask = reachable.get(target, 0)
                for i, source in enumerate(starts):
                    lo, hi = intervals[source]
                    if (mask >> i) & 1 and lo <= upper and lower <= hi:
                        adjacency[i].append(j)
                        indegree[j] += 1
            queue = [i for i, degree in enumerate(indegree) if degree == 0]
            for i in queue:
                for j in adjacency[i]:
                    indegree[j] -= 1
                    if indegree[j] == 0:
                        queue.append(j)
            assert len(queue) == len(starts), 'A directed return cycle remains.'
    print('All 280 final return graphs were independently checked to be acyclic in Python.',
          flush=True)

def run(executable, conjugate, stop=184):
    vertices, phases, edges = initial_graph(conjugate)
    counts = []
    checkpoints = {132: 49218, 140: 27315, 150: 39029, 160: 38893, 170: 24241,
                   180: 7527, 181: 3162, 182: 2029, 183: 964, 184: 0}
    for bits in range(FIRST_BITS, stop + 1):
        if bits == 184:
            verify_empty_return_graphs(vertices, phases, edges, bits, conjugate)
        vertices, phases = cyclic_paths(executable, vertices, phases, edges, bits, conjugate)
        counts.append(len(vertices))
        if bits in checkpoints:
            assert len(vertices) == checkpoints[bits]
        if bits < FIRST_BITS+3 or bits % 5 == 0 or not vertices:
            print(f'{bits} bits: {len(vertices):,} retained vertices.', flush=True)
        if not vertices:
            break
        if bits < stop:
            vertices, phases, edges = lift(vertices, phases, conjugate)
    assert not vertices, 'The claimed exclusion has not been established at this precision.'
    return counts


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cross-check', action='store_true')
    parser.add_argument('--compiler', default='c++')
    options = parser.parse_args()
    with tempfile.TemporaryDirectory() as build:
        exe = Path(build, 'phase_paths')
        cpp = Path(__file__).with_suffix('.cpp')
        subprocess.run([options.compiler, '-O3', '-std=c++17', str(cpp), '-o', str(exe)], check=True)
        result = run(exe, False)
        if options.cross_check:
            assert run(exe, True) == result
            print('Both underlying coordinate graphs give identical counts at every precision.')
