"""Check sample radicands by continued fractions independently of the unit proof."""
from math import gcd, isqrt


def square_multiplier(n):
    """Return s such that n/s^2 is squarefree."""
    s = 1
    for p in range(2, isqrt(n) + 1):
        while n % (p * p) == 0:
            n //= p * p
            s *= p
    return s


def first_pell_unit(d):
    """First continued-fraction convergent of sqrt(d) with norm +1 or -1."""
    root = isqrt(d)
    m, denominator, a = 0, 1, root
    prev_u, u, prev_v, v = 0, 1, 1, 0
    while True:
        prev_u, u = u, a * u + prev_u
        prev_v, v = v, a * v + prev_v
        if abs(u * u - d * v * v) == 1:
            return u, v
        m = denominator * a - m
        denominator = (d - m * m) // denominator
        a = (root + m) // denominator


def check(n):
    s = square_multiplier(n)
    h, y = n // (s * s), n * s
    odd_part = h if h % 2 else h // 2
    successes = 0
    for j in range(1, 100):
        t = odd_part * (1 + 2 * odd_part * j)
        other = y * y * t + 2
        assert gcd(t, other) == 1
        if square_multiplier(t) != 1 or square_multiplier(other) != 1:
            continue
        d = t * other
        k = s * s * d
        assert d % 4 in (2, 3)
        assert first_pell_unit(d) == (1 + y * y * t, y)
        assert gcd(k, y // s) == n
        assert k < 10**6 * n**14
        successes += 1
        if successes == 3:
            return
    raise AssertionError(("Too few squarefree parameters in test range", n))


if __name__ == "__main__":
    for n in range(1, 51):
        check(n)
    print("150 distinct-parameter witnesses checked for n = 1 through 50.")
