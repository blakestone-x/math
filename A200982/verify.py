"""Direct power sums compared with the prime-factor classification."""
from math import lcm


def factor(n):
    result = {}
    p = 2
    while p*p <= n:
        while n%p == 0:
            result[p] = result.get(p,0)+1
            n //= p
        p += 1
    if n>1:
        result[n] = 1
    return result


def carmichael(factors):
    return lcm(*(2**(a-2) if p==2 and a>=3 else (p-1)*p**(a-1)
                 for p,a in factors.items()))


def valuation(n,p):
    h = 0
    while n%p == 0:
        h += 1
        n //= p
    return h


def qualifies(f,lam,l,r):
    if lam % l**r:
        return False
    if 2 in f:
        return l==2 and f[2]>=2 and valuation(lam,2)==r and lam>2**r
    if l in f:
        return False
    vals = [valuation(p-1,l) for p in f]
    return max(vals)>=r and max(vals)-min(vals)<r


def verify():
    pairs = [(ell,r) for ell in (2,3,5,7) for r in range(1,5)]
    comparisons = 0
    for n in range(3,1201):
        f = factor(n)
        lam = carmichael(f)
        for ell,r in pairs:
            if lam%ell**r==0:
                exponent = lam//ell**r
                direct = sum(pow(k,exponent,n) for k in range(1,n))%n==0
                assert qualifies(f,lam,ell,r)==direct,(n,ell,r)
                comparisons += 1
    print(f'{comparisons} direct modular sums through N=1200 '
          'across the 16 choices of prime and exponent.')


if __name__ == '__main__':
    verify()
