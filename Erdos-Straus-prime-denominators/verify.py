"""Compare the two divisor formulas with a search over the middle denominator."""
from math import isqrt


def is_prime(n):
    return n >= 2 and all(n % j for j in range(2, isqrt(n) + 1))


def square_divisors(n):
    divisors = [1]
    q = 2
    while q * q <= n:
        exponent = 0
        while n % q == 0:
            n //= q
            exponent += 1
        if exponent:
            divisors = [d * q**j for d in divisors for j in range(2 * exponent + 1)]
        q += 1
    if n > 1:
        divisors = [d * n**j for d in divisors for j in range(3)]
    return divisors


def count_by_divisors(p, x, a):
    ds = square_divisors(x)
    one = sum((d + p*x) % a == 0 for d in ds)
    two = sum(d <= x and (d + x) % a == 0 for d in ds)
    return one, two


def count_directly(p, x, a):
    counts = [0, 0, 0]
    b = p*x
    for y in range(b // a + 1, 2*b // a + 1):
        z, rem = divmod(b*y, a*y - b)
        if rem == 0:
            assert x < y <= z
            counts[(y % p == 0) + (z % p == 0)] += 1
    assert counts[0] == 0
    return tuple(counts[1:])


if __name__ == "__main__":
    cells = diagonal = empty = 0
    for p in filter(is_prime, range(3, 302)):
        for m in range(2, min(11, p)):
            for a in range(1, min(45, p)):
                if (p + a) % m:
                    continue
                x = (p + a) // m
                actual = count_directly(p, x, a)
                assert actual == count_by_divisors(p, x, a), (p, m, a, actual)
                cells += 1
                diagonal += (2*x) % a == 0
                empty += actual == (0, 0)
    print(f"{cells} exact comparisons, {diagonal} with equal Type II denominators, "
          f"{empty} with neither type.")
