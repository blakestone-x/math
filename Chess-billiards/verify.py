"""Exact checks for the continued-fraction test and its chessboard realization."""
from fractions import Fraction as F
from itertools import product
from math import floor


def distance_integer(x):
    nearest = floor(x + F(1, 2))
    return abs(x - nearest), nearest, (1 if x >= nearest else -1)


def drift_sieve(a, b, maximum_steps=25):
    """A certificate for rational drift on terminating inputs; None on timeout."""
    l = min(a, b)/(a+b)
    t = l*(1-l)
    u = a*b/(a+b)
    if a == b:
        return a
    stack = []
    for _ in range(maximum_steps):
        x, j, sign = distance_integer(u)
        if x == 0 or x >= l:
            d = F(2*j) + sign*int(x != 0)
            for nearest, orientation in reversed(stack):
                d = 2*nearest + orientation/d
            return d
        stack.append((j, sign))
        u = t/x
    return None


def travel_coordinate(y, m):
    whole = y//2
    z = y-2*whole
    return whole + (m*z if z <= 1 else m+(1-m)*(z-1))


def half_turn(v, m):
    j = floor(v)
    x = v-j
    if x <= m:
        return j + m+(1-m)*x/m
    return j + 1+m*(x-m)/(1-m)


def advance_column(column, height, a, b):
    """Trace actual grid edges one by one, using rational geometry."""
    remaining_x = F(1)
    while remaining_x:
        row = floor(height)
        slope = (a, b)[(column+row)%2]
        step_x = min(remaining_x, (row+1-height)/slope)
        remaining_x -= step_x
        height += slope*step_x
    return height


CORNERS = ((F(0), F(0)), (F(1), F(0)), (F(1), F(1)), (F(0), F(1)))


def boundary_point(t):
    t %= 4
    edge = int(t)
    u = t-edge
    x, y = CORNERS[edge]
    xx, yy = CORNERS[(edge+1)%4]
    return (x+(xx-x)*u, y+(yy-y)*u)


def perimeter(z):
    x, y = z
    if y == 0:
        return x
    if x == 1:
        return 1+y
    if y == 1:
        return 3-x
    assert x == 0
    return 4-y


def chord(z, slope):
    """Independently intersect the four square edge lines with the given line."""
    x,y = z
    candidates = set()
    for u in (0,1):
        v = y+slope*(u-x)
        if 0 <= v <= 1:
            candidates.add((F(u),v))
        v = x+(u-y)/slope
        if 0 <= v <= 1:
            candidates.add((v,F(u)))
    candidates.discard(z)
    assert len(candidates) <= 1
    return candidates.pop() if candidates else z


def walk(z, moves):
    for slope in moves:
        z = chord(z,slope)
    return z


def fixed_set(a,b,period):
    """Rebuild S^period on its complete piecewise-affine partition."""
    moves = [a,-b]*period
    base_breaks = {s:set(CORNERS) | {chord(c,s) for c in CORNERS} for s in (a,-b)}
    cuts = {F(0),F(4)}
    for j,s in enumerate(moves):
        for z in base_breaks[s]:
            cuts.add(perimeter(walk(z,reversed(moves[:j]))))
    cuts = sorted(cuts)
    output = []
    for x in cuts:
        val = perimeter(walk(boundary_point(x),moves))%4
        while output and val <= output[-1]:
            val += 4
        output.append(val)
    assert output[-1] == output[0]+4
    fixed = set()
    for x,y,fx,fy in zip(cuts,cuts[1:],output,output[1:]):
        d0,d1 = fx-x,fy-y
        if d0 == d1:
            if d0%4 == 0:
                fixed.update((x%4, y%4, ((x+y)/2)%4))
            continue
        low,high = sorted((d0,d1))
        for n in range(floor(low/4),floor(high/4)+1):
            c = 4*n
            if low <= c <= high:
                fixed.add((x+(y-x)*(c-d0)/(d1-d0))%4)
    for x in fixed:
        z = boundary_point(x)
        assert walk(z,moves)==z
    return fixed,all((fx-x)%4 == 0 for x,fx in zip(cuts,output))


def check():
    values = (F(1,7),F(1,3),F(2,3),F(3,4), F(1), F(4,3), F(7,3))
    traced = 0
    for a,b,y0 in product(values,values,(F(0),F(1,11),F(1,2),F(1),F(7,4))):
        m = b/(a+b)
        s = a*b/(a+b)
        y = y0
        v = travel_coordinate(y,m)
        for n in range(8):
            y = advance_column(n,y,a,b)
            v = half_turn(v+s,m)
            assert travel_coordinate(y+n+1,m)==v
            traced += 1
    print(f"Exact cell-by-cell and section heights agree on {traced} column traversals.")

    periods = 0
    for a,b in product(values,values):
        d = drift_sieve(a,b)
        if d is None:
            continue
        p = d.numerator+d.denominator
        if p > 16:
            continue
        fixed,identity = fixed_set(a,b,p)
        assert fixed
        representative = boundary_point(next(iter(fixed)))
        assert all(walk(representative,[a,-b]*j) != representative for j in range(1,p))
        if a==b:
            assert identity
        periods += 1
    print(f"Independent full boundary partitions confirm {periods} predicted least periods.")

    for k in range(1,5):
        for first in (F(1,3),F(2,7)):
            a = first/k
            b = 1/F(k)-a
            assert drift_sieve(a,b)==F(1,2*k)
            assert fixed_set(a,b,2*k+1)[1]
    assert drift_sieve(F(3,10),F(4,10))==F(1,3)
    fixed,identity = fixed_set(F(3,10),F(4,10),4)
    assert not identity and len(fixed)==4
    print("Figure 9 and seven further common-period examples are periodic everywhere.")
    print("Figure 10 has exactly four fixed points of the two-chord map's fourth iterate.")

    l = F(3,7)
    t = l*(1-l)
    assert t/F(1,7)==2-F(2,7) and t/F(2,7)==1-F(1,7)
    for k in range(2,21):
        a = F(1,2*k)
        b = (1-k*a)/(k-a)
        s = a*b/(a+b)
        assert 0 < s < min(a,b)/(a+b)
        assert 1/(a+b) == k-s
    print("Exact renormalization identities checked for Figure 11 and 19 irrational-drift families.")


if __name__ == "__main__":
    check()
