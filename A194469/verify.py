"""Exact periodic continued fractions and integer-only fractional-part checks."""
from math import isqrt


def period(n):
    a0 = isqrt(n)
    if n == a0*a0:
        return []
    h, d, a = 0, 1, a0
    digits = []
    while True:
        h = d*a-h
        d = (n-h*h)//d
        a = (a0+h)//d
        digits.append(a)
        if a == 2*a0:
            return digits


def curbed(n,q):
    digits = period(n)
    odd_positions = digits if len(digits)%2 else digits[::2]
    return all(a%q == 0 for a in odd_positions)


def first_failure(n,q,limit):
    score = 0
    for k in range(1,limit+1):
        low = isqrt(n*k*k)
        hit = isqrt(q*q*n*k*k) == q*low
        score += q*int(hit)-1
        if score<0:
            return k
    return None


def verify():
    successes = [n for n in range(1,85) if curbed(n,2)]
    failures = [n for n in range(1,89) if not curbed(n,2)]
    assert len(successes)==36 and len(failures)==52
    assert failures[16:21]==[32,33,34,35,40]
    assert first_failure(35,2,1)==1
    for q in range(2,7):
        for n in range(1,401):
            if curbed(n,q):
                assert first_failure(n,q,500) is None
        for b in range(1,61):
            a = b if q==2 else q*b
            for d in range(1,b+1):
                if b%d==0:
                    assert curbed(a*a+d,q)
        assert all(first_failure((a+1)**2-1,q,1)==1 for a in range(1,200))
    print('36 successful entries through 84; 52 failures through 88 with 35 restored. '
          'Exact continued fractions and integer prefix checks passed for q=2..6.')


if __name__ == '__main__':
    verify()
