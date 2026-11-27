"""Exact recurrence certificates for checkerboard avoidance. Requires SymPy."""
from argparse import ArgumentParser
from itertools import product
from math import prod
import sympy as sp

x = sp.Symbol("x")

# a(n) = sum(rec[j-1]*a(n-j)), transcribed from A250956 and A250951--A250955.
EMPIRICAL = {
    2: [4, -1],
    3: [7],
    4: [15, -24, -8],
    5: [27, -57, -46, 30],
    6: [57, -516, 637, 2799, -3639, -100, 429],
    7: [103, -1452, 1999, 25412, -90159, 84285, 261, -20412, 4212],
    8: [217, -9657, 124578, 170544, -10015311, 58649394, -123233697,
        -48475236, 586861054, -648215662, -98069529, 412774803, -157024008,
        -1439235, 9306900, -1445850],
}


def rise_sets(width):
    """All subsets of edges {1,...,w-1} with no consecutive elements."""
    states = []
    def add_from(start, current):
        states.append(tuple(current))
        for pos in range(start, width):
            add_from(pos+2, current+[pos])
    add_from(1, [])
    return states


def transition(width, forbidden_drops, rises):
    """Number of rows with a given rise set and no drops in forbidden_drops."""
    eligible = set(range(1, width)).difference(forbidden_drops)
    if not rises:
        return 2 + len(eligible)
    def free_between(left, right):
        return sum(left < s < right for s in eligible)
    outer_left = 1 + free_between(0, rises[0])
    outer_right = 1 + free_between(rises[-1], width)
    return outer_left * outer_right * prod(
        free_between(left,right) for left,right in zip(rises, rises[1:])
    )


def compressed_matrix(width):
    states = rise_sets(width)
    def reflection(state):
        return tuple(width-j for j in reversed(state))
    orbits = [tuple(sorted({s, reflection(s)})) for s in states if s <= reflection(s)]
    orbits.sort()
    # Empty rise set occupies index zero. Matrix acts on column vectors
    # of continuation counts, constant on each orbit.
    return sp.Matrix([[sum(transition(width, source[0], target) for target in targets)
                       for targets in orbits] for source in orbits])


def coefficients(poly):
    return [poly.nth(i) for i in range(poly.degree()+1)]


def strip_certificate(width):
    matrix = compressed_matrix(width)
    r = matrix.rows
    # det(I-xM)=x^r charpoly(1/x), including possible leading zero coefficients.
    q = matrix.charpoly().all_coeffs()
    v = sp.ones(r, 1)
    terms = []
    for _ in range(r):
        terms.append(v[0])
        v = matrix*v
    p = [sum(q[j]*terms[k-j] for j in range(k+1)) for k in range(r)]
    numerator = sp.Poly.from_list(list(reversed(p)), x, domain=sp.QQ)
    denominator = sp.Poly.from_list(list(reversed(q)), x, domain=sp.QQ)
    # Shift from h>=0 to OEIS's n=h-1>=1 via (F-1-2^w x)/x.
    numerator -= denominator * sp.Poly(1+2**width*x, x, domain=sp.QQ)
    numerator = numerator.exquo(sp.Poly(x,x,domain=sp.QQ))
    common = numerator.gcd(denominator)
    numerator, denominator = numerator.exquo(common), denominator.exquo(common)
    norm = denominator.nth(0)
    numerator = numerator.mul_ground(1/norm)
    denominator = denominator.mul_ground(1/norm)
    assert numerator.gcd(denominator).degree() == 0
    assert numerator.degree() <= denominator.degree()
    return matrix.rows, numerator, denominator


def exhaustive_rows(width):
    states = rise_sets(width)
    for forbidden in states:
        actual = {s: 0 for s in states}
        for row in product((0,1), repeat=width):
            rises = tuple(i for i in range(1,width) if row[i-1] < row[i])
            if all(row[i-1] <= row[i] for i in forbidden):
                actual[rises] += 1
        assert all(actual[s] == transition(width, forbidden, s) for s in states)


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--max-width", type=int, default=8)
    parser.add_argument("--coefficients", action="store_true",
                        help="print the complete reduced numerator and denominator")
    args = parser.parse_args()
    for width in range(2, args.max_width+1):
        if width <= 10:
            exhaustive_rows(width)
        size, p, q = strip_certificate(width)
        coeffs = coefficients(q)
        if width in EMPIRICAL:
            assert coeffs == [1]+[-c for c in EMPIRICAL[width]]
        if width == 4:
            assert coefficients(p) == [0, 209, -391, -128]
        if width == 5:
            assert coefficients(p) == [0, 780, -1852, -1444, 960]
        expected_orders = {9: 23, 10: 39, 11: 58, 12: 97}
        if width in expected_orders:
            assert q.degree() == expected_orders[width]
        print(f"w={width}  reflection states={size}  order={q.degree()}")
        if args.coefficients:
            print(f"  numerator (ascending): {coefficients(p)}")
            print(f"  denominator (ascending): {coeffs}")
