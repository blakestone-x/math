"""Independent enumeration of the n=4 first-corona patches in exact coordinates.

Write z=exp(pi*i/4). Points are coefficients in the integral basis 1,z,z^2,z^3.
This program constructs polygons and compares vertex sets under Euclidean isometries.
It does not import the recurrence, the gap formulas, or the word-orbit code.
"""

from collections import Counter
from functools import cmp_to_key, lru_cache
from itertools import combinations, product


def unit(d):
    i = d % 8
    return tuple((1 if i < 4 else -1) if j == i % 4 else 0 for j in range(4))


def add(p, q):
    return tuple(x + y for x, y in zip(p, q))


def rhombus(p, q, r):
    return tuple(sorted((p, add(p, q), add(p, r), add(add(p, q), r))))


def fans(p, start, end):
    """Visit all increasing chains of rays across an exterior sector."""
    if start == end:
        yield ()
        return
    for direction in range(start + 1, min(start + 3, end) + 1):
        tile = rhombus(p, unit(start), unit(direction))
        for rest in fans(p, direction, end):
            yield (tile,) + rest


def compare_surd(p, q):
    """Exact sign of (p[0]-q[0]) + (p[1]-q[1])*sqrt(2)."""
    a, b = p[0] - q[0], p[1] - q[1]
    if a * b >= 0:
        return (a + b > 0) - (a + b < 0)
    square_diff = a * a - 2 * b * b
    return ((square_diff > 0) - (square_diff < 0)) * (1 if a > 0 else -1)


@lru_cache(maxsize=None)
def spans(tile):
    # 2*cos(d*pi/4) as a pair of integer coefficients of 1 and sqrt(2).
    cosine = ((2, 0), (0, 1), (0, 0), (0, -1), (-2, 0), (0, -1), (0, 0), (0, 1))
    result = []
    for axis in range(4):
        projections = [tuple(sum(p[i] * cosine[(i-axis) % 8][j] for i in range(4))
                             for j in range(2)) for p in tile]
        ordered = sorted(projections, key=cmp_to_key(compare_surd))
        result.append((ordered[0], ordered[-1]))
    return result


@lru_cache(maxsize=None)
def compatible(a, b):
    """A separating axis certifies disjoint interiors for these convex polygons."""
    touching = False
    for (lo, hi), (other_lo, other_hi) in zip(spans(a), spans(b)):
        gap = min(compare_surd(hi, other_lo), compare_surd(other_hi, lo))
        if gap < 0:
            return True
        touching |= gap == 0
    # With a common supporting line, two unit edges sharing an endpoint either
    # coincide or meet only there. This also excludes a vertex in an edge interior.
    return touching and bool(set(a).intersection(b))


def enumerate_patches(k):
    # Outgoing edges, counterclockwise around the marked central tile.
    directions = (0, 4 - k, 4, 8 - k)
    vertices = [(0, 0, 0, 0)]
    for d in directions[:3]:
        vertices.append(add(vertices[-1], unit(d)))
    center_tile = tuple(sorted(vertices))
    center_twice = add(vertices[0], vertices[2])

    @lru_cache(maxsize=None)
    def transform_point(p, rotation, sign):
        # p -> center + z^rotation * (p-center), with optional conjugation.
        doubled = [2 * a - c for a, c in zip(p, center_twice)]
        directions_out = [unit(rotation + sign * i) for i in range(4)]
        result = tuple(c + sum(x * v[j] for x, v in zip(doubled, directions_out))
                       for j, c in enumerate(center_twice))
        return result  # doubled coordinates, including for the identity

    @lru_cache(maxsize=None)
    def transform_tile(tile, rotation, sign):
        return tuple(sorted(transform_point(p, rotation, sign) for p in tile))

    identity_center = transform_tile(center_tile, 0, 1)
    group = [(r, s) for r in range(8) for s in (1, -1)
             if transform_tile(center_tile, r, s) == identity_center]
    by_orbit = Counter()
    fixed = Counter()
    labeled = set()
    for rays in product(*(range(d - 3, d) for d in directions)):
        # A negative angular gap means the two side tiles overlap locally.
        starts = (rays[-1] - 8,) + rays[:-1]
        if any(a > b for a, b in zip(starts, rays)):
            continue
        side_tiles = [rhombus(p, unit(d), unit(r))
                      for p, d, r in zip(vertices, directions, rays)]
        for sectors in product(*(fans(p, a, b) for p, a, b in zip(vertices, starts, rays))):
            tiles = tuple(side_tiles) + sum(sectors, ())
            assert all(compatible(a, b) for a, b in combinations((center_tile,) + tiles, 2))
            images = {g: tuple(sorted(transform_tile(tile, *g) for tile in tiles)) for g in group}
            key = images[0, 1]
            assert key not in labeled
            labeled.add(key)
            by_orbit[min(images.values())] += 1
            fixed.update(g for g in group if images[g] == key)
    return len(labeled), len(by_orbit), Counter(by_orbit.values()), fixed


if __name__ == '__main__':
    for k, expected in [(1, (1452, 385)), (2, (1770, 247))]:
        labeled, orbits, sizes, fixed = enumerate_patches(k)
        assert (labeled, orbits) == expected
        assert sum(sizes.values()) == orbits
        assert sum(s * count for s, count in sizes.items()) == labeled
        print(f'n=4, k={k}: {labeled} labeled patches, {orbits} orbits, '
              f'size distribution {dict(sorted(sizes.items()))}')
        print('fixed patches by (rotation in eighths of a turn, orientation sign)', dict(sorted(fixed.items())))
