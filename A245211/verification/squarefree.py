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


def screened_gaps(r, cs, group, logs, invpow):
    """Put a longest run of unit factors after the last nonunit. Go backward."""
    m = len(cs)
    total = r-m
    least_max = (total+m-1)//m
    # For each possible longest gap, precisely these primitive-root primes
    # force p+1=0 at its two ends. Group equal active sets into intervals.
    cuts = sorted({least_max, total+1} |
                  {q-2 for q in group if least_max < q-2 <= total})
    gaps = [0]*m
    for left,right in zip(cuts,cuts[1:]):
        upper = right-1
        active = tuple(q for q in group if q-2 <= left)
        # For edge c with p'= (2p+1)/c, let y=p+1. Backwards,
        # y=(c*y'+1-c)/2. Across the long unit gap both ends have y=0.
        residues = tuple(((1-cs[-1])*invpow[q][1])%q for q in active)
        def extend(i, remaining, previous_max, y):
            if remaining < max(previous_max,left) or remaining > (i+2)*upper:
                return
            if i < 0:
                if not any(y) and max(left,previous_max)<=remaining<=upper:
                    gaps[-1] = remaining
                    yield tuple(gaps)
                return
            # y is at the end of this gap. The (g+1) vertices in it avoid q
            # precisely when y avoids 1,2,...,2^g modulo q.
            lo = max(0,remaining-(i+1)*upper)
            hi = min(upper,remaining//2,remaining-max(previous_max,left))
            for q,v in zip(active,y):
                if v:
                    hi = min(hi,logs[q][v]-1)
            for g in range(lo,hi+1):
                gaps[i] = g
                c = cs[i]
                new = tuple(((c*v*invpow[q][g]+1-c)*invpow[q][1])%q
                            for q,v in zip(active,y))
                yield from extend(i-1,remaining-g,max(previous_max,g),new)
        yield from extend(m-2,total,0,residues)


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
    logs = {q:{pow(2,j,q):j for j in range(q-1)} for q in group}
    invpow = {q:[pow(2,-j,q) for j in range(r+1)] for q in group}
    dlist = divisors(factors)
    counts = [0,0,0,0]
    solutions = set()
    for part in multiplicative_partitions((1 << r)+1,dlist):
        if len(part)>r:
            continue
        counts[0] += 1
        for cs in distinct_orders(part):
            counts[1] += 1
            for gaps in screened_gaps(r,cs,group,logs,invpow):
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
    parser.add_argument('r',nargs='*',type=int,help='Prime counts to replay; default is every included odd count and r=2.')
    parser.add_argument('--data',type=Path,default=Path(__file__).with_name('factors.json'))
    args=parser.parse_args()
    data=json.loads(args.data.read_text())
    ranks=args.r or sorted(map(int,data['orders']))
    print('r partitions orders gap_patterns survivors_small_divisors solutions seconds',flush=True)
    for r in ranks:
        t=time.monotonic()
        counts,solutions=search(r,data['orders'][str(r)],data['certificates'],data.get('extra_divisors',[]))
        print(r,*counts,','.join(map(str,solutions)) or '-',round(time.monotonic()-t,3),flush=True)


if __name__=='__main__':
    main()
