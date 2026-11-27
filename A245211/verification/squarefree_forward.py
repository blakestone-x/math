"""Exhaustive cycle test for prescribed numbers of distinct primes in A245211."""
import argparse
from collections import Counter
from math import gcd, prod
from pathlib import Path
import json
import time


def is_prime_small(n):
    if n < 2:
        return False
    d = 2
    while d*d <= n:
        if n % d == 0:
            return False
        d += 1 if d == 2 else 2
    return True


def check_prime(p, certs, proven):
    """Lucas primality criterion with the complete factorization of p-1."""
    if p in proven:
        return
    if p < 2048:
        assert is_prime_small(p), p
    else:
        a, factors = certs[str(p)]
        assert 1 < a < p and prod(q**e for q,e in factors) == p-1
        for q,e in factors:
            assert 1 < q < p and e > 0
            check_prime(q, certs, proven)
            assert gcd(pow(a, (p-1)//q, p)-1, p) == 1
        assert pow(a, p-1, p) == 1
    proven.add(p)


def divisors(factors):
    values = [1]
    for p,e in factors:
        values = [d*p**j for d in values for j in range(e+1)]
    return sorted(values)


def multiplicative_partitions(n, all_divisors, least=2):
    """Nondecreasing lists of nonunit factors with product n."""
    yield (n,)
    for d in all_divisors:
        if d*d > n:
            break
        if d >= least and n % d == 0:
            for rest in multiplicative_partitions(n//d, all_divisors, d):
                yield (d,)+rest


def distinct_orders(values):
    """Generate arrangements without the factorial cost of duplicate factors."""
    counts = Counter(values)
    keys = tuple(counts)
    path = []
    def walk():
        if len(path) == len(values):
            yield tuple(path)
            return
        for k in keys:
            if counts[k]:
                counts[k] -= 1
                path.append(k)
                yield from walk()
                path.pop()
                counts[k] += 1
    yield from walk()


def cyclic_orders(values, anchor):
    if anchor is not None:
        first = next(v for v in values if v % anchor == 0)
        rest = list(values)
        rest.remove(first)
        for order in distinct_orders(rest):
            yield (first,)+order
    else:
        for seq in distinct_orders(values):
            if all(seq <= seq[j:]+seq[:j] for j in range(1,len(seq))):
                yield seq


def twin_gap_limit(c, group_primes, r):
    # A string of at least ell-2 unit edges gives ell-1 prime vertices.
    # If 2 generates modulo ell, the value p+1 at both endpoints is 0 mod ell.
    # On opposite sides of c, this requires c=1 mod ell.
    return min((p-2 for p in group_primes if c % p != 1), default=r+1)


def gap_tuples(r, limits):
    m = len(limits)
    gaps = [0]*m
    def extend(i, remaining):
        hi = remaining
        if i and gaps[i-1] >= limits[i]:
            hi = min(hi, limits[i]-1)
        if i == m-1:
            if remaining <= hi and (gaps[0] < limits[0] or remaining < limits[0]):
                gaps[i] = remaining
                yield tuple(gaps)
            return
        for g in range(hi+1):
            gaps[i] = g
            yield from extend(i+1, remaining-g)
    if m == 1:
        if r-1 < limits[0]:
            yield (r-1,)
        return
    yield from extend(0, r-m)


def start_of_cycle(values, gaps):
    a, prefix = 0, 1
    for c,g in zip(values,gaps):
        a = 2*a+prefix
        prefix *= c
        a = (a << g)+((1 << g)-1)*prefix
    return a


def supported_by_exact_divisors(values, gaps, p, primes, hits):
    """Return False on the first proper prime divisor certified in the cycle."""
    original = p
    for c,g in zip(values,gaps):
        p,rem = divmod(2*p+1,c)
        assert rem == 0
        for q in primes:
            if p % q in hits[q][g]:
                return False
        p = ((p+1) << g)-1
    assert p == original
    return True


def full_cycle(values,gaps):
    p = start_of_cycle(values,gaps)
    start = p
    path = []
    for c,g in zip(values,gaps):
        path.append(p)
        p,rem = divmod(2*p+1,c)
        assert rem == 0
        for _ in range(g):
            path.append(p)
            p = 2*p+1
    assert p == start
    return path


def search(r, factors, certs, extras):
    assert r >= 2 and prod(p**e for p,e in factors) == (1 << r)+1
    assert all(e>0 for p,e in factors) and len(set(p for p,e in factors)) == len(factors)
    proven = set()
    for p,e in factors:
        check_prime(p,certs,proven)
    primes = [p for p in range(3,min(251,1 << (r-1))+1,2) if is_prime_small(p)]
    group = [p for p in primes if len({pow(2,j,p) for j in range(p-1)}) == p-1]
    hits = {}
    for p in primes:
        row = [set()]
        for j in range(r):
            row.append(row[-1]|{(pow(2,-j,p)-1)%p})
        hits[p] = row[1:]
    anchor = max((p for p,e in factors if e == 1),default=None)
    dlist = divisors(factors)
    counts = [0,0,0,0]
    solutions = set()
    for part in multiplicative_partitions((1 << r)+1,dlist):
        if len(part)>r:
            continue
        counts[0] += 1
        for cs in cyclic_orders(part,anchor):
            counts[1] += 1
            limits = [twin_gap_limit(c,group,r) for c in cs]
            for gaps in gap_tuples(r,limits):
                counts[2] += 1
                p = start_of_cycle(cs,gaps)
                if not supported_by_exact_divisors(cs,gaps,p,primes,hits):
                    continue
                counts[3] += 1
                path = full_cycle(cs,gaps)
                if len(set(path)) != r:
                    continue
                if any(any(1<d<v and v % d==0 for d in extras) for v in path):
                    continue
                if r==2 and set(path)=={3,7}:
                    solutions.add(21)
                else:
                    raise RuntimeError(f'Unresolved cycle at r={r}: {path}')
    return counts,sorted(solutions)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('r',nargs='*',type=int,help='Prime counts to replay; default is r=2 and all odd counts through 63.')
    parser.add_argument('--data',type=Path,default=Path(__file__).with_name('factors.json'))
    args=parser.parse_args()
    data=json.loads(args.data.read_text())
    ranks=args.r or [2, *range(3,64,2)]
    print('r partitions orders gap_patterns survivors_small_divisors solutions seconds',flush=True)
    for r in ranks:
        t=time.monotonic()
        counts,solutions=search(r,data['orders'][str(r)],data['certificates'],data.get('extra_divisors',[]))
        print(r,*counts,','.join(map(str,solutions)) or '-',round(time.monotonic()-t,3),flush=True)


if __name__=='__main__':
    main()
