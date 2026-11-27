"""Direct checks of the determinant, denominator valuations and power sums."""
from fractions import Fraction
from math import comb


def valuation(q, p):
    q = Fraction(q)
    assert q
    top, bottom = abs(q.numerator), q.denominator
    result = 0
    while top % p == 0:
        top //= p
        result += 1
    while bottom % p == 0:
        bottom //= p
        result -= 1
    return result


def recurrence(u, v, end):
    terms = [Fraction(u), Fraction(v)]
    for n in range(2, end+1):
        terms.append(((7*n*n-7*n+2)*terms[-1]+8*(n-1)**2*terms[-2])/(n*n))
    return terms


def check():
    franel = [sum(comb(n,j)**3 for j in range(n+1)) for n in range(244)]
    assert recurrence(1,2,243) == franel
    for u, v in [(0,1),(3,4),(-4,2),(5,10),(1,11)]:
        seq = recurrence(u,v,243)
        for n in range(1,244):
            assert franel[n-1]*seq[n]-franel[n]*seq[n-1] == Fraction((-8)**(n-1)*(v-2*u),n*n)
        if v == 2*u:
            continue
        for p in [3,5,7,11,13,17,19,23]:
            val = valuation(v-2*u,p)
            if val<2:
                assert valuation(seq[p],p)==val-2
            if all(f%p for f in franel[:p]):
                n, r = p, 1
                while n<244:
                    if 2*r>val:
                        assert valuation(seq[n],p)==val-2*r
                    n*=p
                    r+=1
    for a in range(1,65):
        if a%2:
            for n in range(129):
                assert sum(pow(comb(n,j),a,3) for j in range(n+1))%3 == pow(2,n,3)
        else:
            for p in range(2,130):
                if all(p%q for q in range(2,1+int(p**0.5))):
                    assert sum(pow(comb(p-1,j),a,p) for j in range(p))%p==0
    for a in range(2,65):
        h = 2 if a%2 else min(a,3+valuation(a,2))
        least = a
        for n in range(1,129):
            row = [comb(n,k) for k in range(n+1)]
            gap = sum(v**a for v in row) - 2**n.bit_count()
            assert gap % 2**h==0
            if gap:
                least=min(least,valuation(gap,2))
        assert least==h
    print('Five initial pairs and 243 determinants per pair checked.')
    print('Independent binomial sums agree with the integer Franel solution.')
    print('Denominator valuations checked at odd primes and their applicable powers.')
    print('Avoided-prime witnesses checked at exponents 1 through 64.')
    print('Sharp uniform power checked at exponents 2 through 64 and rows 1 through 128.')


if __name__=='__main__':
    check()
