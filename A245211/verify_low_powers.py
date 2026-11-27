"""Exact check of the profiles with smallest exponent two; no external libraries."""
from bisect import bisect_right
from functools import cache
from itertools import permutations
from math import gcd, isqrt, prod


def primes_to(limit):
    marked = [True] * (limit+1)
    marked[:2] = [False, False]
    for p in range(2, isqrt(limit)+1):
        if marked[p]:
            for m in range(p*p, limit+1, p):
                marked[m] = False
    return [p for p in range(limit+1) if marked[p]]


def H(p,e):
    return (((e+1)*p-e-2)*p**(e+1)+1)//(p-1)**2


@cache
def vals(e,m):
    out=set()
    for x in range(1,m):
        if gcd(x,m)==1:
            t=0
            for j in range(1,e+2):
                t=(x*t+j)%m
            out.add(t)
    return out


@cache
def paired(a,b,m):
    return {u*v%m for u in vals(a,m) for v in vals(b,m)}


def run():
    mods=(8,16,32,64,3,9,27,81,5,25,7,49,11,13,17,19,23,29,31,37,41,43)
    patterns=[]
    for b in range(2,26):
        for a in range(b,10*b+7):
            d=3*(a+1)*(b+1)
            if all(any((t*u-d-1)%m==0 for t in paired(a,b,m) for u in vals(2,m))
                   for m in mods if m<d//2):
                patterns.append((a,b,2))
    assert patterns==[(6,2,2),(50,6,2)]
    print('All profiles surviving modular tests:',patterns)
    base_limit=max(3*(1+prod(e+1 for e in triple))+1 for triple in patterns)
    first_primes=primes_to(base_limit)
    rows=[]
    for triple in patterns:
        d=prod(e+1 for e in triple)
        for i,j,k in sorted(set(permutations(triple))):
            for x in first_primes:
                if x>3*(d+1)+1: break
                if x<=i*(d//(i+1)): continue
                A=H(x,i)
                if any(not any((A*pow(x,-i,m)*v-d-1)%m==0 for v in paired(j,k,m))
                       for m in mods if m<d//2): continue
                base=(d+1)*x**i
                gap=base-(j+1)*(k+1)*A
                if gap>0:
                    upper=1+(2*base)//gap
                    if upper>x: rows.append((x,i,j,k,d,A,base,upper))
    upper=max(row[-1] for row in rows)
    primes=primes_to(upper)
    checked=0
    roots=[]
    for x,i,j,k,d,A,base,upper in rows:
        low=bisect_right(primes,max(x,j*(d//(j+1))))
        for y in primes[low:bisect_right(primes,upper)]:
            W=A*H(y,j)
            M=base*y**j
            G=M-(k+1)*W
            if G<=0: continue
            z=(k*W+G-1)//G
            if z<=max(y,k*(d//(k+1))) or z%2==0: continue
            checked+=1
            if W*H(z,k)==M*z**k:
                roots.append((x,i,y,j,z,k))
    print('Largest second-prime bound actually sieved:',max(row[-1] for row in rows))
    print('Full integral products tested:',checked)
    print('Integral equalities:',roots)
    assert not roots


if __name__=='__main__':
    if not __debug__:
        raise SystemExit('Run with Python assertions enabled.')
    run()
