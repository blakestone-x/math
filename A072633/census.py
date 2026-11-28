"""Exhaust the A072633 rounding-rule exceptions for 10^9 <= n <= 10^1000.

The analytic inputs are equations (2)-(3) and Remark 10 of arXiv:2611.28637.
Arithmetic in this certificate is entirely rational.
"""
from fractions import Fraction
from math import isqrt


def log_interval(digits):
    """ln(2) by 2*atanh(1/3), with rigorous integer rounding and tail."""
    scale = 10**digits
    lower = 0
    power = 3
    count = 0
    while 4*power <= 9*scale:
        lower += 2*scale // ((2*count+1)*power)
        power *= 9
        count += 1
    return Fraction(lower, scale), Fraction(lower+count+1, scale)


def convergents(lower, upper, limit):
    """Compare both simple CF expansions through the first denominator > limit."""
    x, y = lower.numerator, lower.denominator
    z, w = upper.numerator, upper.denominator
    pp, p, qq, q = 0, 1, 1, 0
    index = 0
    while True:
        a, r = divmod(x,y)
        b, s = divmod(z,w)
        if a != b:
            raise ArithmeticError("insufficient precision for continued fractions")
        x,y,z,w = y,r,w,s
        pp,p,qq,q = p,a*p+pp,q,a*q+qq
        if q > limit:
            return
        yield index,p,q
        index += 1


def main():
    lower_limit, limit = 10**9, 10**1000
    log_lo, log_hi = log_interval(2100)
    alpha_lo, alpha_hi = 2/log_hi, 2/log_lo
    gamma_lo = Fraction(25,12) - 3*log_hi
    gamma_hi = Fraction(25,12) - 3*log_lo
    if not (gamma_hi + Fraction(116,lower_limit) < Fraction(1,250)):
        raise ArithmeticError("uniform gamma bound")
    results = []
    candidates = 0
    for index,p,q in convergents(alpha_lo,alpha_hi,limit):
        if p % 2 == 0:
            continue
        e_lo = q*(p-q*alpha_hi)
        e_hi = q*(p-q*alpha_lo)
        if e_hi < 0:
            continue
        if e_lo <= 0:
            raise ArithmeticError("insufficient precision for signed error")
        cutoff_square = Fraction(1,125)/e_lo
        max_t = min(limit//q, isqrt(cutoff_square.numerator//cutoff_square.denominator))
        for t in range(1,max_t+1,2):
            n,h = t*q,t*p
            if n < lower_limit:
                continue
            M = (h+3)//2
            dlo = M*(h-n*alpha_hi)/2
            dhi = M*(h-n*alpha_lo)/2
            if not (0 < dlo <= dhi < 1 and M > n):
                raise ArithmeticError("rounding candidate")
            candidates += 1
            if dhi < gamma_lo-Fraction(87,M):
                results.append((index,t,p,q))
                print(f"exception  CF={index}  multiplier={t}  digits={len(str(n))}", flush=True)
            elif not dlo > gamma_hi+Fraction(116,M):
                raise ArithmeticError("overlapping analytic error bounds")
    print("Number of retained candidates:",candidates)
    print("Number of counterexamples:",len(results))
    for j,t,p,q in results:
        print(f"CF={j}, multiplier={t}, exponent={t*q}, actual term={(t*p+3)//2}")
    return results


if __name__ == "__main__":
    main()
