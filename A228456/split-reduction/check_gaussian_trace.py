"""Check the Gaussian trace at split primes by polynomial remainders and Newton sums."""
from math import comb, isqrt


def gaussian_trace(p):
    n = (p - 1) // 3
    a = [(-1)**i * comb(n, i) * comb(n+i, i) % p for i in range(n+1)]
    inverse_lead = pow(a[n], -1, p)
    inverses = [0] + [pow(i, -1, p) for i in range(1, p)]
    r = [sum(a[i] * inverses[i-j] for i in range(j+1,n+1)) % p for j in range(n)]
    # s^(p-1) R + 3s^p R'; the coefficient of s^(n-1) in its remainder,
    # divided by the leading coefficient, is the derivative-weighted root sum.
    poly = [0] * (p-1) + [c*(1+3*i) % p for i,c in enumerate(r)]
    for i in range(len(poly)-1,n-1,-1):
        q = poly[i]*inverse_lead % p
        for j in range(n+1):
            poly[i-n+j] = (poly[i-n+j]-q*a[j])%p
    rational_trace = poly[n-1]*inverse_lead % p
    powers = [n]
    for k in range(1,p):
        lower = sum(a[n-i]*powers[k-i] for i in range(1,min(n,k-1)+1))
        boundary = k*a[n-k] if k<=n else 0
        powers.append(-(lower+boundary)*inverse_lead % p)
    logs = sum(inverses[i]*powers[i] for i in range(1,p))%p
    value = (logs + rational_trace*pow(3,-1,p))%p
    B = comb(2*n,n)
    quotient = (pow(B,p-1,p*p)-1)//p
    return value, quotient


if __name__ == '__main__':
    tested = []
    for p in range(7,1000,6):
        if any(p%k==0 for k in range(2,isqrt(p)+1)):
            continue
        value, target = gaussian_trace(p)
        assert value == target, (p,value,target)
        tested.append(p)
    print(f'Trace agrees with the Fermat quotient at {len(tested)} split primes through {tested[-1]}.')
