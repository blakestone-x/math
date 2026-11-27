"""Independent direct-integer cross-checks for the two computational subroutines."""
from functools import cache
from math import isqrt


@cache
def literal_moment(base, exponent):
    # No quotient formula.
    value = 0
    for j in range(exponent, -1, -1):
        value = base * value + j + 1
    return value


def check_prime_intervals(widths, witnesses, lower):
    # Direct bit sieve and literal divisibility of the full integer H_e(x).
    # A positive witness only needs primality and divisibility. When the
    # helper returns zero the entire advertised interval must be exhausted.
    empty = []
    for (x, e), upper in widths.items():
        value = literal_moment(x, e)
        t = witnesses[x, e]
        if t:
            assert lower < t <= upper and value % t == 0
            assert all(t % d for d in range(2, isqrt(t)+1))
        else:
            empty.append((upper, value))
    largest = max((n for n, _ in empty), default=lower)
    small = []
    for n in range(2, isqrt(largest)+1):
        if all(n % p for p in small if p*p <= n):
            small.append(n)
    width = 2**19
    for start in range(lower+1, largest+1, width):
        stop = min(start+width, largest+1)
        live = bytearray([1])*(stop-start)
        for p in small:
            if p*p >= stop:
                break
            first = max(p*p, ((start+p-1)//p)*p)
            if first < stop:
                live[first-start::p] = bytes((stop-1-first)//p+1)
        for index, flag in enumerate(live):
            if flag:
                p = start+index
                for upper, value in empty:
                    if p <= upper:
                        assert value % p != 0
    print('independent interval checks:', len(widths), 'including', len(empty), 'empty intervals')


def remaining_by_bisection(x, i, fixed, f, e, d):
    w = literal_moment(x, i) * literal_moment(fixed, f)
    target = (d+1)*x**i*fixed**f
    if (e+1)*w >= target:
        return 0

    def sign(t):
        value = w*literal_moment(t, e) - target*t**e
        return (value > 0) - (value < 0)

    low, high = x+1, x+1
    if sign(low) < 0:
        return 0
    while sign(high) > 0:
        high *= 2
    while low < high:
        middle = (low+high)//2
        if sign(middle) > 0:
            low = middle+1
        else:
            high = middle
    return low if low != fixed and low % 2 and sign(low) == 0 else 0
