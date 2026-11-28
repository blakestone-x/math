"""Independent completion of all surviving boxes by local prime divisibility."""
import argparse
from array import array
from bisect import bisect_right
from math import gcd, isqrt


def primes_through(bound):
    odd = bytearray(b'\x01') * ((bound+1)//2)
    odd[0] = 0
    for p in range(3, isqrt(bound)+1, 2):
        if odd[p//2]:
            start = p*p//2
            odd[start::p] = b'\x00' * ((len(odd)-1-start)//p+1)
    primes = array('I', [2])
    primes.extend(2*j+1 for j, allowed in enumerate(odd) if allowed)
    return primes


def moment(x, e):
    total = 0
    for coefficient in range(e+1, 0, -1):
        total = total*x+coefficient
    return total


def integer_root(value, degree):
    if degree == 1:
        return value
    low, high = 1, 1 << ((value.bit_length()+degree-1)//degree)
    while low < high:
        mid = (low+high)//2
        if mid**degree < value:
            low = mid+1
        else:
            high = mid
    return low if low**degree == value else None


def remaining_base(i, j, x, t, unknown_weight, D):
    # The residual in the normalized equation strictly decreases with v.
    W = moment(x, i)*moment(t, j)
    M = (D+1)*x**i*t**j
    gap = M-(unknown_weight+1)*W
    if gap <= 0:
        return None
    def difference(v):
        return W*moment(v, unknown_weight)-M*v**unknown_weight
    low, high = 2, 2+unknown_weight*W//gap
    while low < high:
        mid = (low+high)//2
        if difference(mid) > 0:
            low = mid+1
        else:
            high = mid
    return low if difference(low) == 0 else None


def check(path):
    boxes = [tuple(map(int, line.split())) for line in open(path)]
    small = primes_through(max(u for _, _, _, _, u in boxes))
    jobs = []
    for i, j, k, lo, hi in boxes:
        D = (i+1)*(j+1)*(k+1)
        for x in small[bisect_right(small,lo-1):bisect_right(small,hi)]:
            H = moment(x,i)
            g = (D+1)*x**i-(j+1)*(k+1)*H
            assert g>0
            bound = 1+2*(D+1)*x**i//g
            jobs.append((i,j,k,x,H,D,bound))
    primes = primes_through(max(v[-1] for v in jobs))
    fixed_by_divisor = 0
    power_cases = 0
    evaluated = 0
    for i, j, k, x, H, D, bound in jobs:
        reduced = H//gcd(H,D+1)
        assert reduced > 1
        known = None
        for p in primes:
            if p > bound:
                break
            if reduced % p == 0:
                known = p
                break
        if known is not None:
            fixed_by_divisor += 1
            if known <= x:
                continue
            assignments = [(known,j,k,True),(known,k,j,False)]
        else:
            power_cases += 1
            # y <= bound and y cannot divide reduced, so reduced=z^h.
            assignments = [(t,k,j,False) for h in range(1,k+1)
                           if (t := integer_root(reduced,h)) is not None and t>x]
        for t, exponent, other, is_middle in assignments:
            evaluated += 1
            v=remaining_base(i,exponent,x,t,other,D)
            if v is not None and (x<t<v if is_middle else x<v<t):
                raise AssertionError((x,t,v,i,exponent,other))
    print('Intervals, smallest-prime rows:', len(boxes),len(jobs))
    print('Rows with a local divisor, rows requiring integer roots:',fixed_by_divisor,power_cases)
    print('Exact monotone completions:',evaluated)
    print('Ordered integer equalities: 0')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('intervals')
    check(parser.parse_args().intervals)
