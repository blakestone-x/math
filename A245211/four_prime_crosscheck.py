"""Independent exact search. Bound q by monotonicity with r=s=q."""
from fractions import Fraction
from functools import cache
from itertools import count
from math import isqrt


@cache
def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def check():
    rows = considered = 0
    for exponent in range(1, 23):
        c = 8 * exponent + 9
        for p in range(8 * exponent + 1, 32*c + 8):
            if not prime(p):
                continue
            # Build the integer moment by Horner evaluation, including parity.
            h = 0
            for coefficient in range(exponent + 1, 0, -1):
                h = p*h + coefficient
            if h % 2 == 0:
                continue
            rows += 1
            rhs = c * p**exponent
            for q in count(4*exponent + 5, 2):
                if h * (2*q + 1)**3 <= rhs * q**3:
                    break
                if q == p or not prime(q):
                    continue
                considered += 1
                ratio = Fraction(rhs*q, h*(2*q+1))
                u, v = ratio.numerator, ratio.denominator
                if not 4*v < u < 5*v:
                    continue
                pairs = set()
                # If one of the primes is v, use the linear equation for the other.
                if u-4*v > 2 and (2*v+1) % (u-4*v-2) == 0:
                    pairs.add(tuple(sorted((v, (2*v+1)//(u-4*v-2)))))
                # With product v, 4(r-s)^2 = (u-4v-1)^2 - 16v.
                s2 = u-4*v-1
                g2 = s2*s2-16*v
                if g2 >= 0 and isqrt(g2)**2 == g2:
                    gap = isqrt(g2)
                    if (s2+gap) % 4 == 0 and (s2-gap) % 4 == 0:
                        pairs.add(((s2-gap)//4,(s2+gap)//4))
                for r,s in pairs:
                    if q < r < s and p not in (r,s):
                        assert h*(2*q+1)*(2*r+1)*(2*s+1) == rhs*q*r*s
                        assert not (prime(r) and prime(s)), (exponent,p,q,r,s)
    print(f"{rows} exponent/base pairs; {considered} triples below the cubic upper bound; zero prime completions")


if __name__ == '__main__':
    check()
