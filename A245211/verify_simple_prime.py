"""Exact enumeration for the three-prime theorem, using the Python standard library."""
from collections import Counter
from functools import cache
from itertools import permutations
from math import gcd, isqrt, prod
from pathlib import Path
import subprocess
import sys

LIMIT = 131_072
MODULI = (8, 16, 32, 3, 9, 27, 5, 25, 7, 49, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43)


def sieve(limit):
    flags = bytearray([1]) * (limit + 1)
    flags[:2] = bytes(2)
    for p in range(2, isqrt(limit) + 1):
        if flags[p]:
            flags[p*p::p] = bytes((limit - p*p) // p + 1)
    return [p for p, prime in enumerate(flags) if prime]


PRIMES = sieve(LIMIT)
BLOCKS = [PRIMES[i:i+256] for i in range(0, len(PRIMES), 256)]
PRIME_PRODUCTS = [(prod(block), block) for block in BLOCKS]


def moment(x, e):
    return (((e + 1)*x - (e + 2)) * x**(e + 1) + 1) // (x - 1)**2


@cache
def values(e, m):
    # F_e reduced on the units modulo m. Inversion permutes those units.
    return {sum((e+1-j)*pow(x, j, m) for j in range(e+1)) % m
            for x in range(1, m) if gcd(x, m) == 1}


@cache
def pairs(e, f, m):
    return {s*t % m for s in values(e, m) for t in values(f, m)}


def admitted_pattern(a, b, d):
    for m in MODULI:
        if m >= d//2:
            continue
        if not any((s*t - d-1) % m == 0 for s in pairs(a, b, m) for t in values(1, m)):
            return False
    return True


def admitted_base(x, i, j, k, d):
    for m in MODULI:
        if m >= d//2:
            continue
        v = (moment(x, i) % m) * pow(x, -i, m) % m
        if not any((v*t - d-1) % m == 0 for t in pairs(j, k, m)):
            return False
    return True


def small_factor(n):
    for product, primes in PRIME_PRODUCTS:
        common = gcd(n, product)
        if common > 1:
            return next(p for p in primes if common % p == 0)
    return 0


def exact_root(n, h):
    if h == 1:
        return n
    low, high = 1, 1 << ((n.bit_length()+h-1)//h)
    while high-low > 1:
        middle = (high+low)//2
        if middle**h < n:
            low = middle
        else:
            high = middle
    return high if high**h == n else 0


def remaining(x, i, fixed, f, e, d):
    w = moment(x, i)*moment(fixed, f)
    g = (d+1)*x**i*fixed**f - (e+1)*w
    if g <= 0:
        return 0
    t = (e*w + g-1)//g
    if t <= x or t == fixed or t % 2 == 0:
        return 0
    if w*moment(t, e) == (d+1) * x**i * fixed**f * t**e:
        return t
    return 0


def run(helper, cross_check=False):
    if cross_check:
        from cross_check_simple_prime import check_prime_intervals, remaining_by_bisection
    rows = []
    widths = {}
    patterns = Counter()
    fixed_x = Counter()
    for b in range(1, 17):
        for a in range(b, 7*b+4):
            d = 2*(a+1)*(b+1)
            if not admitted_pattern(a, b, d):
                continue
            patterns[b] += 1
            for i, j, k in sorted(set(permutations((a, b, 1)))):
                for x in PRIMES:
                    if x > 3*(d+1)+1:
                        break
                    if x <= i*(d//(i+1)) or not admitted_base(x, i, j, k, d):
                        continue
                    w = moment(x, i)
                    g = (d+1)*x**i-(j+1)*(k+1)*w
                    if g <= 0:
                        continue
                    upper = 1 + (2*(d+1)*x**i)//g
                    if upper <= x:
                        continue
                    B = w//gcd(w, d+1)
                    assert B > 1 and x < LIMIT and d+1 < LIMIT
                    t = (2*x+1) if i == 1 else small_factor(B)
                    if t and t <= x:
                        continue
                    fixed_x[b] += 1
                    key = (x, i)
                    if not t and upper > LIMIT:
                        widths[key] = max(widths.get(key, 0), upper)
                    rows.append((x, i, j, k, d, B, upper, t))
    keys = sorted(widths)
    data = [f'{LIMIT} {len(keys)}'] + [f'{x} {i} {widths[x, i]}' for x, i in keys]
    raw = subprocess.check_output([helper], input='\n'.join(data)+'\n', text=True)
    found = dict(zip(keys, map(int, raw.split()), strict=True))
    if cross_check:
        check_prime_intervals(widths, found, LIMIT)
    equalities = set()
    checked = 0
    for x, i, j, k, d, B, upper, t in rows:
        if not t:
            t = found.get((x, i), 0)
        if t:
            if i != 1:
                assert B % t == 0
            # For i=1 the proof already requires 2x+1 to be one of y,z.
            roles = [(t,j,k,True), (t,k,j,False)]
        else:
            # A possible smaller prime y <= upper has been ruled out as a
            # divisor of B. Thus B=z^h, h<=k, including the case h=1.
            roles = [(z,k,j,False) for h in range(1, k+1) if (z := exact_root(B, h))]
        for fixed, f, e, fixed_is_y in roles:
            if fixed <= x or (fixed_is_y and fixed > upper):
                continue
            checked += 1
            other = remaining(x, i, fixed, f, e, d)
            if cross_check:
                assert other == remaining_by_bisection(x, i, fixed, f, e, d)
            if not other:
                continue
            y, z = (fixed,other) if fixed_is_y else (other,fixed)
            if x < y < z:
                equalities.add((x,i,y,j,z,k))
    # Include composite final values to make the verification independent
    # of probable-prime tests. Each surviving equality is examined directly.
    print('admissible exponent pairs by smaller exponent:', sorted(patterns.items()))
    print('ordered smallest-prime rows after sieves:', len(rows))
    print('extended prime-divisor intervals:', len(keys), 'largest endpoint:', max(widths.values()))
    print('single-candidate completions:', checked)
    print('integer equalities at ordered odd bases:', sorted(equalities))
    for x, i, y, j, z, k in equalities:
        assert any(n % p == 0 and p < n for n in (y,z) for p in PRIMES)
    print('three-prime fixed points with a simple prime divisor: 0')


if __name__ == '__main__':
    run(str(Path(sys.argv[1]).resolve()), '--cross-check' in sys.argv[2:])
