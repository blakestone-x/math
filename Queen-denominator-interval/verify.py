"""Construct explicit queen vertices from the radix proof, and check their ranks."""
from math import gcd
from random import Random


FORMS = {"x": (1, 0), "y": (0, 1), "sum": (1, 1), "diff": (1, -1)}
PRIME = 1_000_003


def full_rank(rows):
    """A nonzero determinant modulo PRIME certifies full rank over the rationals."""
    pivots = {}
    for row in rows:
        r = {j: value % PRIME for j, value in row.items() if value % PRIME}
        while r:
            j = min(r)
            coeff = r[j]
            if j not in pivots:
                inv = pow(coeff, -1, PRIME)
                pivots[j] = {h: a*inv % PRIME for h, a in r.items()}
                break
            for h, a in pivots[j].items():
                remaining = (r.get(h, 0) - coeff*a) % PRIME
                if remaining:
                    r[h] = remaining
                elif h in r:
                    del r[h]
        else:
            return False
    return True


class Board:
    def __init__(self, denominator):
        self.denominator = denominator
        self.points = []  # integer numerators, with common board scale d
        self.rows = []

    def add(self, x, y):
        assert 0 <= x <= self.denominator and 0 <= y <= self.denominator
        i = len(self.points)
        self.points.append((x, y))
        return i

    def equal(self, i, j, form):
        assert i != j
        c, d = FORMS[form]
        xi, yi = self.points[i]
        xj, yj = self.points[j]
        assert c*(xi-xj) + d*(yi-yj) == 0
        self.rows.append({2*i: c, 2*i+1: d, 2*j: -c, 2*j+1: -d})

    def fix(self, i, axis, high=False):
        assert self.points[i][axis] == (self.denominator if high else 0)
        self.rows.append({2*i+axis: 1})

    def check(self):
        assert gcd(self.denominator, *(x for point in self.points for x in point)) == 1
        assert len(self.rows) == 2*len(self.points)
        assert full_rank(self.rows)


def spiral(k):
    points = [(0, 0), (1, -1), (0, -2)]
    edges = [(0, 1, "sum"), (0, 2, "x"), (1, 2, "diff")]
    for i in range(3, k):
        x, y = points[i-1]
        if i%2:
            new_y = points[i-3][1]
            points.append((x+y-new_y, new_y))
            edges.extend([(i-3, i, "y"), (i-1, i, "sum")])
        else:
            new_x = points[i-3][0]
            points.append((new_x, y+new_x-x))
            edges.extend([(i-3, i, "x"), (i-1, i, "diff")])
    if k%2:
        points = [(y, x) for x, y in points]
        edges = [(i,j,{"x":"y","y":"x"}.get(m,m)) for i,j,m in edges]
    min_x = min(x for x,_ in points)
    min_y = min(y for _,y in points)
    points = [(x-min_x,y-min_y) for x,y in points]
    low, high = sorted((0,1), key=lambda i:points[i][0])
    assert points[high][0] == points[low][0]+1
    return points, edges, low, high


def build_table(board, maximum):
    origin = board.add(0,0)
    board.fix(origin,0)
    board.fix(origin,1)
    unit = board.add(1,0)
    board.fix(unit,1)
    one = board.add(0,1)
    board.fix(one,0)
    board.equal(unit,one,"sum")
    table = [origin,one]
    for j in range(2,maximum+1):
        v = board.add(1,j-1)
        board.equal(v,unit,"x")
        board.equal(v,table[j-1],"y")
        w = board.add(0,j)
        board.fix(w,0)
        board.equal(v,w,"sum")
        table.append(w)
    return table


def multiply_add(board, shape, source, digit):
    points, edges, lo, hi = shape
    u = board.points[source][1]
    v = board.points[digit][1]
    labels = [board.add(u*x,u*y) for x,y in points]
    for i,j,m in edges:
        board.equal(labels[i],labels[j],m)
    left = min(range(len(points)), key=lambda i:points[i][0])
    bottom = min(range(len(points)), key=lambda i:points[i][1])
    right = max(range(len(points)), key=lambda i:points[i][0])
    board.fix(labels[left],0)
    board.fix(labels[bottom],1)
    t = board.add(u*points[hi][0],0)
    board.equal(t,labels[hi],"x")
    board.fix(t,1)
    z = board.add(u*points[lo][0],u)
    board.equal(z,labels[lo],"x")
    board.equal(z,source,"y")
    board.equal(t,z,"sum")
    top = u*points[right][0]
    arg = board.add(top,v)
    board.equal(arg,labels[right],"x")
    board.equal(arg,digit,"y")
    result = board.add(0,top+v)
    board.fix(result,0)
    board.equal(arg,result,"sum")
    return result


def certificate(k, d, b, shape=None):
    board = Board(d)
    if d == 1:
        corner = board.add(0,0)
        board.fix(corner,0)
        board.fix(corner,1)
    else:
        digits, t = [], d
        while t:
            t, digit = divmod(t,b)
            digits.append(digit)
        if shape is None:
            shape = spiral(k)
        table = build_table(board,min(d,b-1))
        p = table[digits.pop()]
        blocks = len(digits)
        while digits:
            p = multiply_add(board,shape,p,table[digits.pop()])
        board.fix(p,1,True)
        assert len(board.points) == 2*min(d,b-1)+1 + (k+4)*blocks
    board.check()


def semiqueen_template(k):
    """Primitive shape from the signed coordinate cycle in the companion paper."""
    pts = [(-1,-1),(2,-1),(-1,2)]
    edges = [(0,1,"y"),(0,2,"x"),(1,2,"sum")]
    kinds = [0,1,2,0,1,2]
    signs = [1,-1,1,-1,1,-1]

    def value(i,kind):
        x,y = pts[i]
        return (x,y,-x-y)[kind]

    holders = [max(range(3), key=lambda i:signs[h]*value(i,kinds[h])) for h in range(6)]
    for step in range(k-3):
        j = step%6
        vals = [None]*3
        for h in ((j-1)%6,(j+1)%6):
            m = kinds[h]
            vals[m] = value(holders[h],m)
            edges.append((len(pts),holders[h],("x","y","sum")[m]))
        vals[kinds[j]] = -sum(v for v in vals if v is not None)
        assert all(v%3==2 for v in vals)
        holders[j] = len(pts)
        pts.append(tuple(vals[:2]))
    a,b = (min(p[i] for p in pts) for i in (0,1))
    pts = [((x-a)//3,(y-b)//3) for x,y in pts]
    if max(y for x,y in pts)>max(x for x,y in pts):
        pts = [(y,x) for x,y in pts]
        edges = [(i,j,{"x":"y","y":"x"}.get(m,m)) for i,j,m in edges]
    lo,hi = next((i,j) for i in range(3) for j in range(3) if pts[j][0]-pts[i][0]==1)
    return pts,edges,lo,hi


def enumerate_shapes(through=7):
    """All distinct integer shapes obtainable by successive intersections, up to square symmetry."""
    from itertools import combinations, product

    directions = list(FORMS.values())
    def canonical(points):
        variants = []
        for swap, sx, sy in product((False,True), (-1,1), (-1,1)):
            pts = [(sx*(y if swap else x),sy*(x if swap else y)) for x,y in points]
            a,b = min(x for x,y in pts), min(y for x,y in pts)
            variants.append(tuple(sorted((x-a,y-b) for x,y in pts)))
        return min(variants)

    frontier = {canonical([(0,0),(1,0)]), canonical([(0,0),(1,1)])}
    maxima = [1]
    counts = [len(frontier)]
    for n in range(3,through+1):
        nxt = set()
        for pts in frontier:
            intercept = [set(a*x+b*y for x,y in pts) for a,b in directions]
            for i,j in combinations(range(4),2):
                a,b = directions[i]
                c,d = directions[j]
                det = a*d-b*c
                for first,second in product(intercept[i],intercept[j]):
                    xx,yy = d*first-b*second, a*second-c*first
                    scale = 2 if xx%det or yy%det else 1
                    updated = tuple((scale*x,scale*y) for x,y in pts)
                    p = (scale*xx//det,scale*yy//det)
                    if p in updated:
                        continue
                    nxt.add(canonical((*updated,p)))
        frontier = nxt
        widths = [max(max(x for x,y in pts),max(y for x,y in pts)) for pts in frontier]
        maxima.append(max(widths))
        counts.append(len(frontier))
    return maxima,counts


def main():
    fib = [0,1]
    for _ in range(75):
        fib.append(sum(fib[-2:]))
    for k in range(3,76):
        points, _, _, _ = spiral(k)
        assert max(x for x,_ in points) == fib[k]
        assert max(y for _,y in points) == fib[k-1]
    maxima, counts = enumerate_shapes()
    assert maxima == fib[2:8]
    print(f"Exhaustive successive intersections at q=2 through 7: {counts} shapes, maxima {maxima}.")
    checked = 0
    rng = Random(20261126)
    for k in range(3,11):
        b = fib[k]
        ds = set(range(1,2*b+4))
        for level in range(1,7):
            for delta in (-1,0,1):
                ds.add(b**level+delta)
        ds.update(rng.randrange(2,b**7) for _ in range(12))
        for d in sorted(ds):
            assert d % PRIME != 0
            certificate(k,d,b)
            checked += 1
    semichecks = 0
    for k in range(4,17):
        shape = semiqueen_template(k)
        b = max(x for x,y in shape[0])
        if b < 2:
            continue
        assert all(m in ("x","y","sum") for i,j,m in shape[1])
        for d in sorted(set([2,b-1,b,b+1,2*b+1,b**3-1,b**3+1])):
            certificate(k,d,b,shape)
            semichecks += 1
    print(f"Verified {semichecks} ordinary-semiqueen radix vertices using only three moves.")
    print("Verified both Fibonacci spans for 73 spiral sizes.")
    print(f"Verified board containment, every equation, exact denominators, and full rank "
          f"of {checked} radix vertices across eight radices (including k=3 with radix 2).")


if __name__ == "__main__":
    main()
