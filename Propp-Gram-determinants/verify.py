"""Exact evaluations and independent graph constructions for Propp 26 and 27."""
from collections import Counter
from fractions import Fraction
from functools import cache
from itertools import combinations
from math import comb, factorial, prod

import mpmath as mp
import sympy as sp
from sympy.polys.matrices import DomainMatrix


def choose(n, k):
    return comb(n, k) if 0 <= k <= n else 0


def det(rows):
    if not rows:
        return 1
    return int(sp.Matrix(rows).det(method="domain-ge"))


def gram(rows):
    if not rows:
        return 1
    matrix = sp.Matrix(rows)
    return int((matrix * matrix.T).det(method="domain-ge"))


def planar_hexagon(a, b, c, d):
    """Build unit triangles geometrically, identifying adjacent triangles by sides."""
    side = a + b + c + d

    def inside(vertex):
        x, y = vertex
        return 0 <= x <= side - a and 0 <= y <= side - b and c <= x + y <= side

    def edges(triangle):
        return {tuple(sorted(e)) for e in combinations(triangle, 2)}

    up, down = [], []
    for x in range(side):
        for y in range(side):
            middle = ((x + 1, y), (x, y + 1))
            for corner, faces in (((x, y), up), ((x + 1, y + 1), down)):
                triangle = (*middle, corner)
                if all(map(inside, triangle)):
                    faces.append(edges(triangle))
    assert len(up) - len(down) == d
    return [[int(bool(p & q)) for p in up] for q in down]


def macmahon(a, b, c):
    return prod((Fraction(factorial(i)*factorial(a+b+i),
                          factorial(a+i)*factorial(b+i)) for i in range(c)),
                start=Fraction(1))


def hexagon_formula(a, b, c, d):
    t = a + b + c + d - 1
    moment = [[0] * d for _ in range(d)]
    for i in range(t-a+1):
        for j in range(t-b+1):
            k = t-i-j
            if not 0 <= k <= t-c:
                continue
            vector = []
            for l in range(d):
                coeff = sum((-1)**(c-q+k) * comb(c, q) * choose(b+l, i-q) *
                            choose(a+d-1-l, j-c+q) for q in range(c+1))
                vector.append(factorial(i) * factorial(j) * factorial(k) * coeff)
            for l in range(d):
                for h in range(d):
                    moment[l][h] += vector[l] * vector[h]
    boundary = prod(factorial(b+s)*factorial(t-b-s) for s in range(d))
    result = macmahon(a, b+d, c)**2 * det(moment) / boundary**2
    assert result.denominator == 1
    return result.numerator


def checkerboard(m, n, fool):
    """Real Kasteleyn signing: one sign reversal around each elementary square."""
    rows = [(u, v) for u in range(1, 2*m, 2)
            for v in (range(1, 2*n, 2) if fool else range(0, 2*n+1, 2))]
    cols = [(u, v) for u in range(0, 2*m+1, 2)
            for v in (range(0, 2*n+1, 2) if fool else range(1, 2*n, 2))]
    def entry(p, q):
        dx, dy = q[0]-p[0], q[1]-p[1]
        if abs(dx) != 1 or abs(dy) != 1:
            return 0
        return -1 if (dx, dy) == (1, -1) else 1
    return [[entry(p, q) for q in cols] for p in rows]


@cache
def half_path(n):
    """Q_n with x^(n mod 2) Q_n(x^2) equal to the path characteristic polynomial."""
    x = sp.Symbol("x")
    return sp.Poly(sum((-1)**j * comb(n-j, j) * x**(n//2-j)
                       for j in range(n//2+1)), x)


def fool_root(r, s):
    u, v = r//2, s//2
    x = sp.Symbol("x")
    q = half_path(s)
    transformed = sp.Poly(sum(q.nth(j)*16**j*x**(v-j) for j in range(v+1)), x)
    # SymPy's low-level resultant can swap unequal degrees. The product is positive.
    value = abs(int(half_path(r).resultant(transformed)))
    return 2**(r*s-4*u*v) * value


def toeplitz_coefficient(m, k):
    return (-1)**abs(k) * sum(2**(m-2*j)*comb(m+1, 2*j+1)*comb(2*j, j+k)
                              for j in range(abs(k), m//2+1))


@cache
def toeplitz(m, size):
    return det([[toeplitz_coefficient(m, i-j) for j in range(size)] for i in range(size)])


def aztec_formula(m, n):
    m, n = sorted((m, n))
    d = n-m
    return 2**(m*(m+1)) * toeplitz(m, d//2) * toeplitz(m, (d+1)//2)


def subset_value(m, t):
    """Numerical evaluation of the root-subset sum, independent of integer Toeplitz entries."""
    h = m//2
    alpha = 2**(m-2*h)*comb(m+1, 2*h+1)
    roots = []
    for j in range(1, h+1):
        angle = mp.pi*j/(m+1)
        roots.extend((1/mp.cos(angle) + sign*mp.tan(angle))**2 for sign in (1,-1))
    total = mp.mpf(0)
    for subset in combinations(range(2*h), h):
        outside = set(range(2*h)).difference(subset)
        numerator = prod(roots[i]**(t+h) for i in subset)
        denominator = prod(roots[i]-roots[j] for i in subset for j in outside)
        total += mp.mpf(numerator)/denominator
    return alpha**t*total


def manyama(order):
    size = (order-1)//2
    cos2 = [mp.cos(j*mp.pi/order)**2 for j in range(1,size+1)]
    power = 4**(2*size**2) if order%2 else 2*4**(2*size*(size+1))
    return power * prod(1-x*y for x in cos2 for y in cos2)


def main():
    counters = Counter()
    for a in range(4):
        for b in range(4):
            for c in range(4):
                for d in range(4):
                    direct = gram(planar_hexagon(a, b, c, d))
                    assert direct == hexagon_formula(a, b, c, d), (a,b,c,d,direct)
                    counters["hexagons"] += 1
    published = 2**8 * 3**3 * 7**6
    assert hexagon_formula(3,3,3,1) == published
    for m in range(1, 8):
        for n in range(m, 13):
            k = sp.Matrix(checkerboard(m,n,False))
            g = k*k.T
            assert int(g.det(method="domain-ge")) == aztec_formula(m,n), (m,n)
            nullity = g.rows - DomainMatrix.from_Matrix(g-4*sp.eye(g.rows)).rank()
            assert nullity == (m%2)*(n-1)+(n%2)*(m-1), (m,n,nullity)
            counters["Aztec rectangles"] += 1
    for r in range(9):
        for s in range(r, 10):
            assert gram(checkerboard(r,s,True)) == fool_root(r,s)**2, (r,s)
            counters["fool's rectangles"] += 1
    table = [1,2,15,384,32625,9085440,8238791743,24233379889152]
    assert [fool_root(r,r) for r in range(8)] == table
    with mp.workdps(160):
        for m in range(1,11):
            for t in range(8):
                assert abs(subset_value(m,t)-toeplitz(m,t)) < mp.mpf("1e-75"), (m,t)
        for n in range(1,16):
            assert abs(manyama(n)-fool_root(n-1,n-1)) < mp.mpf("1e-75"), n
    print("Exact independent Gram determinants:", dict(counters))
    print("Independent exact ranks of G-4I:", counters["Aztec rectangles"])
    print("160-digit cross-checks: 80 root-subset sums and 15 parity products")
    print("Honeycomb (3,4,3,4,3,4):", published)
    print("All eight tabulated fool's-diamond values equal the positive square roots.")
    print("First two further roots:", fool_root(8,8), fool_root(9,9))


if __name__ == "__main__":
    main()
