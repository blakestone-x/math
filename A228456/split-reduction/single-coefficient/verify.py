"""Exact fast test of the split-prime target via a universal coefficient."""
from math import isqrt
import sys

def primes(bound):
    sieve = bytearray(b'\x01') * (bound + 1)
    for i in range(2, isqrt(bound) + 1):
        if sieve[i]:
            sieve[i*i::i] = bytes((bound - i*i)//i + 1)
    return [p for p in range(7, bound + 1, 6) if sieve[p]]

def multiply(f, g, cap, p):
    # Encode coefficients as non-overlapping integer digits. This is exact
    # because every pre-reduction coefficient is smaller than 256**width.
    if not f or not g: return []
    width = (min(len(f),len(g)).bit_length() + 2*p.bit_length() + 7)//8
    n = min(cap, len(f)+len(g)-1)
    def pack(poly):
        return int.from_bytes(b''.join(a.to_bytes(width,'little') for a in poly),'little')
    z = (pack(f)*pack(g)) % (1 << (8*width*n))
    raw = z.to_bytes(width*n,'little')
    return [int.from_bytes(raw[i:i+width],'little') % p for i in range(0,len(raw),width)]

def inverse_poly(f, n, p):
    inv = [pow(f[0],-1,p)]
    while len(inv) < n:
        m = min(2*len(inv),n)
        product = multiply(f[:m], inv, m, p)
        err = [(-u)%p for u in product]
        err[0] = (err[0] + 2)%p
        inv = multiply(inv, err, m, p)
    return inv

def check(p):
    n = (p-1)//3
    inv = [0,1] + [0]*(p-2)
    for j in range(2,p):
        inv[j] = - (p//j)*inv[p%j] % p
    # A^*(z) = 2F1(-n,-n;-2n;z); its coefficients through n
    # are the corresponding 2F1(1/3,1/3;2/3;z) coefficients modulo p.
    f = [1]
    for j in range(1,n+1):
        f.append(f[-1]*(j-1-n)**2*inv[j]*inv[(j-1-2*n)%p] % p)
    finv = inverse_poly(f,n+1,p)
    derivative = [j*f[j]%p for j in range(1,n+1)]
    dlog = multiply(derivative,finv,n,p)
    logs = [0]+[dlog[j-1]*inv[j]%p for j in range(1,n+1)]
    inv_squared = multiply(finv,finv,n+1,p)
    partial = 0
    coefficient = 0
    for j,v in enumerate(inv_squared):
        partial = (partial + v)%p
        coefficient = (coefficient + logs[n-j]*partial)%p
    a = 1
    for j in range(1,n+1):
        a = a*(n+j)*pow(j,-1,p*p)%(p*p)
    qp = (pow(a,p-1,p*p) - 1)//p
    return (coefficient + a*a*qp)%p == 0

if __name__=='__main__':
    bound = int(sys.argv[1]) if len(sys.argv)>1 else 5000
    tested = primes(bound)
    for p in tested:
        if not check(p): raise ValueError(f'counterexample p={p}')
    print(f'Coefficient identity and hence the split-prime prediction hold at all {len(tested)} split primes through {bound}.')
