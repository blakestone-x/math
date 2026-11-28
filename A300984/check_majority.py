"""Independent divisor-by-divisor audit of the first three prime-majority rows."""
from math import isqrt

from sympy import divisors, factorint, isprime, primerange


def squarefree(value):
    return value > 0 and all(e == 1 for e in factorint(value).values())


def divisor_sums(value):
    ds = divisors(value)
    first = sum(d for d in ds if squarefree(d))
    return first, sum(ds) - first


def represented(bound):
    bases = set()
    # The necessary shape from Proof.lean is used here. No congruence sieve
    # or closed divisor-sum formula from the fast implementation is used.
    for p in primerange(3, isqrt(bound // 4) + 1):
        power = p * p
        while 4 * power <= bound and p not in bases:
            candidate = 4 * power
            while candidate <= bound:
                if all(squarefree(s) for s in divisor_sums(candidate)):
                    bases.add(p)
                    break
                candidate *= 2
            power *= p
    return bases


def belongs(p):
    return all(not isprime(d - 1) for d in divisors(p + 1) if d < p + 1)


if __name__ == "__main__":
    assert divisor_sums(4 * 937**2) == (2814, 6149535)
    assert all(squarefree(s) for s in divisor_sums(3511876))
    assert not belongs(937)
    # The set printed explicitly in the 2018 comment on A300984.
    printed = {13, 37, 61, 73, 109, 157, 181, 193, 229, 277, 313, 373, 397,
               409, 421, 433, 457, 541, 601, 613, 661, 673, 709, 733, 757, 769,
               829, 853, 877, 997, 1009, 1021, 1033, 1069, 1093, 1117, 1129,
               1153, 1201, 1213, 1237, 1297, 1381, 1429, 1453, 1489}
    for m, total, qualifying in [(7, 47, 39), (8, 132, 98), (9, 382, 269)]:
        primes = represented(10**m)
        if m == 7:
            assert primes == printed | {937}
        assert len(primes) == total and sum(map(belongs, primes)) == qualifying
        print(f"10^{m}: {qualifying} of {total} represented bases belong to A082539.")
