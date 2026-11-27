"""Independent sanity check from the original A134559 remainder sums.

Only Python's standard library is used. This is not an input to the Lean proof.
"""
from math import gcd, isqrt


def prime(n):
    return n > 1 and all(n % d for d in range(2, isqrt(n) + 1))


def remainder_sums(n):
    sums = [0] * ((n + 1) // 2)
    for u in range(1, n + 1):
        r = n % u
        if r < len(sums):
            sums[r] += u
    return sums


p, k = 54217, 2737
assert prime(p) and prime((p + 1) // 2)
fiber = [u for u in range(1, p + 1) if p % u == k]
assert fiber == [2860, 3432, 3960, 4290, 4680, 5148, 5720, 6435,
                 8580, 10296, 12870, 17160, 25740, 51480]
assert sum(fiber) == 162651 == 3 * p
sums = remainder_sums(p)
assert sums[k] == 162651
product_mod_p = 1
for factor in sums:
    product_mod_p = product_mod_p * factor % p
assert gcd(product_mod_p, p) == p
print(f"p={p}, (p+1)/2={(p+1)//2}: both prime")
print(f"b_{p}({k})={sum(fiber)}=3*p")
print(f"gcd(P({p}),{p})={gcd(product_mod_p,p)}")
print("PASS: the proposed characterization fails.")
