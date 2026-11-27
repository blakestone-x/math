"""Verify the prime-density bound, the Gauss-sum lift and the certified literal gaps."""
import argparse
import csv
import re
import subprocess
from fractions import Fraction
from functools import cache
from math import gcd, isqrt, prod
from pathlib import Path
from tempfile import TemporaryDirectory

from sympy import jacobi_symbol, n_order, sqrt_mod

HERE = Path(__file__).resolve().parent
# In the final two rows the last prime is the remaining cofactor.
FACTORS = [[11], [101], [73,137], [17,5882353], [353,449,641,1409,69857],
           [19841,976193,6187457,834427406578561],
           [1265011073,15343168188889137818369,515217525265213267447869906815873],
           [257,15361,453377], [10753,8253953,9524994049,73171503617]]
for a in (7,8):
    FACTORS[a].append((10**(2**a)+1)//prod(FACTORS[a]))


def trial_prime(n):
    if n % 2 == 0:
        return n == 2
    return n > 1 and all(n % d for d in range(3, isqrt(n)+1, 2))


def factor_checks(vcert):
    big = set()
    for a, primes in enumerate(FACTORS):
        assert prod(primes) == 10**(2**a)+1
        assert len(primes) == len(set(primes))
        for p in primes:
            if p < 10**18:
                assert trial_prime(p)
            else:
                big.add(p)
    blocks = (HERE/"prime-certificates.txt").read_text().split("[MPU - Primality Certificate]")
    roots = set()
    with TemporaryDirectory() as tmp:
        for i, body in enumerate(blocks[1:]):
            n = int(re.search(r"Proof for:\s*N\s+(\d+)", body).group(1))
            roots.add(n)
            if vcert:
                file = Path(tmp)/f"factor-{i}.cert"
                file.write_text("[MPU - Primality Certificate]"+body)
                subprocess.run([vcert, str(file)], check=True, capture_output=True)
    assert roots == big
    misses = [1-Fraction(1, 4)] + [1-Fraction(1, 2**len(row)) for row in FACTORS[1:]]
    assert 1-prod(misses) == Fraction(227568931, 268435456)


def lift_root(p, width, root):
    """One width multiplication by p, with no factorization of the new modulus."""
    b = 10**width
    old = b+1
    assert (root*root-p) % old == 0 and gcd(p,old)==1
    new = b**p+1
    h = new//old
    z = -b
    gauss = 0
    for j in range(p-1, 0, -1):
        chi = 1 if pow(j, (p-1)//2, p) == 1 else -1
        gauss = ((gauss+chi)*z) % h
    if p % 4 == 3:
        assert width % 2 == 0
        gauss = gauss*pow(10, width*p//2, h) % h
    root = root + old*((gauss-root)*pow(old,-1,h) % h)
    assert (root*root-p) % new == 0
    return width*p, max(root, new-root)


def blocks(c, d, k):
    base = 10**d
    x,y = divmod(k*k, base)
    return base//10 <= x <= y < base and y-x == c


def obstruction(c):
    """False means this certificate is inconclusive. True excludes every d >= 10."""
    v = c
    while v % 2 == 0:
        v //= 2
    coprime = v
    while coprime % 5 == 0:
        coprime //= 5
    period = int(n_order(10, coprime)) if coprime > 1 else 1

    @cache
    def symbol(residue):
        return int(jacobi_symbol(1+pow(10, 10*period+residue, v), v))

    candidates = [d for d in range(period) if symbol(d) != -1]
    for a, primes in enumerate(FACTORS):
        if any(pow(c % p, (p-1)//2, p) == p-1 for p in primes):
            continue
        common = gcd(period, 2**(a+1))
        if any((d-2**a) % common == 0 for d in candidates):
            return False
    # For c <= 1000 the power of two dividing the period is at most 512.
    two_part = period & -period
    assert two_part <= 512
    if not any(d % two_part == 0 for d in candidates):
        return True
    e = pow(2, 9, period)
    seen = set()
    while e not in seen:
        seen.add(e)
        if symbol(e) != -1:
            return False
        e = 2*e % period
    return True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--vcert", help="path to the standalone MPU certificate verifier")
    args = parser.parse_args()
    factor_checks(args.vcert)
    if not args.vcert:
        print("Large-factor certificates are present. Pass --vcert to replay their primality proofs.")
    with (HERE/"gap-witnesses.csv").open() as f:
        witnesses = {}
        for row in csv.DictReader(f):
            c,d,k = (int(row[key]) for key in ("difference","block_digits","square_root"))
            assert c not in witnesses and 0 <= c <= 1000 and blocks(c,d,k)
            witnesses[c] = (d,k)
    root = next(k for k in range(101) if (k*k-701) % 101 == 0)
    assert lift_root(701,2,root) == witnesses[701]
    for p,d in [(5,1),(13,2),(19,2)]:
        roots = sqrt_mod(p,10**d+1,all_roots=True)
        if roots and (p % 4 == 1 or d % 2 == 0):
            new_d,k = lift_root(p,d,int(roots[0]))
            assert blocks(p,new_d,k)
    absent, finite = [], {}
    for c in range(1, 1001):
        if not obstruction(c):
            continue
        small = [(d,int(k)) for d in range(1,10)
                 for k in sqrt_mod(c,10**d+1,all_roots=True) if blocks(c,d,int(k))]
        if small:
            finite[c] = small
        else:
            assert c not in witnesses
            absent.append(c)
    assert finite == {3:[(1,5),(1,6)],6:[(2,39),(2,62)],24:[(2,78)],30:[(2,38),(2,63)]}
    data = [int(v) for v in (HERE/"absent-gaps.txt").read_text().split()]
    assert absent == data and len(absent) == 67
    assert len(witnesses) == 860
    print("860 exact witnesses and 67 all-width exclusions in differences 0 through 1000.")
    print("Finite nonempty witness sets:", finite)
    print("Prime residue-class density: 227568931 / 268435456.")


if __name__ == "__main__":
    main()
