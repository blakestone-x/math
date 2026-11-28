"""Exact checks for the boundary and triangle constructions. Python 3 only."""
from fractions import Fraction as F
from itertools import combinations, product
from math import gcd, lcm


def eliminate(matrix, pivots):
    """Gauss-Jordan reduction. Return None for a singular leading square."""
    rows = [list(map(F, row)) for row in matrix]
    for col in range(pivots):
        pivot = next((i for i in range(col, len(rows)) if rows[i][col]), None)
        if pivot is None:
            return None
        rows[pivot], rows[col] = rows[col], rows[pivot]
        scale = rows[col][col]
        rows[col] = [a / scale for a in rows[col]]
        for i, row in enumerate(rows):
            if i != col and row[col]:
                coeff = row[col]
                rows[i] = [a - coeff * b for a, b in zip(row, rows[col])]
    return rows


def edge_row(i, j, move, labels):
    row = [0] * (2 * labels)
    c, d = move
    row[2*i], row[2*i+1] = d, -c
    row[2*j], row[2*j+1] = -d, c
    return row


def three_label_census(s):
    """Enumerate all possible bases of move rows and coordinate fixations."""
    moves = [(a, 1) for a in range(1, s+1)]
    edges = [edge_row(i, j, m, 3) for i, j in combinations(range(3), 2) for m in moves]
    vertices = set()
    for rank in range(5):  # Two independent translations force rank <= 4.
        for free in combinations(range(6), rank):
            fixed = sorted(set(range(6)) - set(free))
            for chosen in combinations(edges, rank):
                # Solve for all free coordinates as functions of fixed corners.
                matrix = [[e[j] for j in free] + [-e[j] for j in fixed] for e in chosen]
                reduced = eliminate(matrix, rank)
                if reduced is None:
                    continue
                for values in product((0, 1), repeat=len(fixed)):
                    point = [F(0)] * 6
                    for j, value in zip(fixed, values):
                        point[j] = F(value)
                    for j, row in zip(free, reduced):
                        point[j] = sum((a*b for a, b in zip(row[rank:], values)), F(0))
                    if all(0 <= x <= 1 for x in point):
                        vertices.add(tuple(point))
    triangle = set()
    for z in vertices:
        xy = list(zip(z[::2], z[1::2]))
        (x, y), (u, v), (w, t) = xy
        if (u-x)*(t-y) == (w-x)*(v-y):
            continue
        if all(any(p[0]-r[0] == c*(p[1]-r[1]) for c, _ in moves)
               for p, r in combinations(xy, 2)):
            triangle.add(lcm(*(a.denominator for a in z)))
    return len(vertices), max(lcm(*(a.denominator for a in z)) for z in vertices), sorted(triangle)


def check_system(points, fixes, attacks, moves):
    n = 2*len(points)
    coords = [F(c) for point in points for c in point]
    assert all(0 <= c <= 1 for c in coords)
    rows = []
    for label, axis, value in fixes:
        assert value in (0, 1)
        row = [0] * n
        row[2*label+axis] = 1
        assert coords[2*label+axis] == value
        rows.append(row)
    for i, j, m in attacks:
        assert i != j and m in moves
        row = edge_row(i, j, m, len(points))
        assert sum(a*b for a, b in zip(row, coords)) == 0
        rows.append(row)
    assert len(rows) >= n and eliminate(rows, n) is not None
    return lcm(*(c.denominator for c in coords))


def check_trident(k):
    moves = [(0,1), (1,1), (-1,1)]
    points = [(0, 0), (1, 0)]
    fixes = [(0,0,0), (0,1,0), (1,0,1), (1,1,0)]
    attacks = []
    last = 1
    for i in range(1, k+1):
        x = F(1, 2**i)
        q = len(points)
        points.append((x, x))
        attacks.extend([(0, q, moves[1]), (last, q, moves[2])])
        if i < k:
            last = len(points)
            points.append((x, 0))
            fixes.append((last, 1, 0))
            attacks.append((q, last, moves[0]))
    assert check_system(points, fixes, attacks, moves) == 2**k


def check_shear(N, k, even):
    moves = [(N+i,1) for i in range(3)]
    points = [(0,0), (1,F(1,N)), (0,F(1,N*(N+1)))]
    fixes = [(0,0,0), (0,1,0), (1,0,1), (2,0,0)]
    attacks = [(0,1,moves[0]), (1,2,moves[1])]
    for _ in range(k):
        last = len(points)-1
        y = points[last][1]
        q = len(points)
        points.append((F(N*(N+2),2)*y, F(N+2,2)*y))
        points.append((0,F(N+2,2*(N+1))*y))
        fixes.append((q+1,0,0))
        attacks.extend([(0,q,moves[0]), (last,q,moves[2]), (q,q+1,moves[1])])
    assert points[-1][1].denominator == N*(N+1)*(2*(N+1))**k
    if even:
        j = len(points)
        points.append((0,1))
        fixes.extend([(j,0,0), (j,1,1)])
    denominator = check_system(points, fixes, attacks, moves)
    assert denominator >= N*(N+1)*(2*(N+1))**k
    if N == 1_000_001:
        assert denominator > 2*(N+1)*20**len(points)


def check_semiqueens():
    moves = [(0,1), (1,0), (-1,1)]
    pts = [(2,2),(3,1),(4,0), (0,5),(3,2),(4,1), (0,2),(2,0), (0,9),(4,5)]
    pts = [(F(x,9),F(y,9)) for x,y in pts]
    fixes = [(i,axis,int(v)) for i,p in enumerate(pts) for axis,v in enumerate(p) if v in (0,1)]
    attacks = []
    for i,j in combinations(range(len(pts)),2):
        dx,dy = (pts[i][k]-pts[j][k] for k in (0,1))
        for c,d in moves:
            if d*dx==c*dy:
                attacks.append((i,j,(c,d)))
    assert len(attacks)+len(fixes)==28
    assert check_system(pts,fixes,attacks,moves) == 9

    def unsigned(p,kind):
        x,y = p
        return (x,y,-x-y)[kind]

    kinds = [0,1,2,0,1,2]
    signs = [1,-1,1,-1,1,-1]
    points = [(-1,-1),(2,-1),(-1,2)]
    edges = [(0,1,moves[1]),(0,2,moves[0]),(1,2,moves[2])]
    stored = [max(range(3),key=lambda i: signs[j]*unsigned(points[i],kinds[j])) for j in range(6)]
    seq = []
    for n in range(36):
        j = n%6
        values = [None]*3
        for h in ((j-1)%6,(j+1)%6):
            kind = kinds[h]
            values[kind] = unsigned(points[stored[h]],kind)
            edges.append((len(points),stored[h],moves[kind]))
        values[kinds[j]] = -sum(x for x in values if x is not None)
        assert all(x%3==2 for x in values)
        stored[j] = len(points)
        points.append(tuple(values[:2]))
        seq.append(signs[j]*values[kinds[j]])
        assert seq[-1] > 0
        if n >= 5:
            assert seq[-1] == seq[-2]+seq[-6]
        a,b = (min(p[k] for p in points) for k in (0,1))
        w,h = max(p[0] for p in points)-a, max(p[1] for p in points)-b
        span = max(w,h)
        assert 2*span >= seq[-1]
        chosen = [(next(i for i,p in enumerate(points) if p[0]==a),0,0),
                  (next(i for i,p in enumerate(points) if p[1]==b),1,0)]
        axis = int(h>w)
        chosen.append((max(range(len(points)),key=lambda i:points[i][axis]),axis,1))
        fitted = [(F(x-a,span),F(y-b,span)) for x,y in points]
        assert check_system(fitted,chosen,edges,moves) == span//3



def main():
    expected = {3: (244, 6, [4]), 4: (448, 12, [4, 6, 9])}
    for s, result in expected.items():
        census = three_label_census(s)
        assert census == result
        print(f"{s} moves: {census[0]} labelled vertices, maximum {census[1]}, "
              f"triangle denominators {census[2]}.")
    for N in range(1,13):
        for s in range(3,9):
            triangles = [b*(c-a)//gcd(c-b,b-a)
                         for a,b,c in combinations(range(N,N+s),3)]
            assert max(triangles) == (N+s-2)*(s-1)
    check_semiqueens()
    print("Verified the 10-semiqueen counterexample and the first 36 cyclic semiqueen constructions.")
    for k in range(1,11):
        check_trident(k)
    for N in [1, 3, 17, 1_000_001]:
        for k in range(8):
            for even in (False, True):
                check_shear(N, k, even)
    print("Verified the triangle formula for 72 move sets, ten dyadic trident vertices, "
          "and 64 boundary-transfer vertices by exact arithmetic and full rank.")


if __name__ == "__main__":
    main()
