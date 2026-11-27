"""Exact certificate for three equilateral foldings of a single rod chain."""
from math import lcm

SQUARE_CLASS = 132405
DISCRIMINANT = 3 * SQUARE_CLASS
CERTIFICATE = (
    (396, 29767, 147137, 205943),
    (748, 7471, 272281, 384991),
    (4756, 354481, 1766521, 2472961),
)


def pell_power(exponent):
    x, y = 1, 0
    for _ in range(exponent):
        x, y = 2521 * x + 4 * DISCRIMINANT * y, 4 * x + 2521 * y
    assert x * x - DISCRIMINANT * y * y == 1
    return x, y


def triangular(index):
    return index * (index + 1) // 2


def check(exponent):
    x, y = pell_power(exponent)
    n = (x - 1) // 2
    perimeter = triangular(n)
    folds = set()
    for h, a, b, c in CERTIFICATE:
        assert b * b - a * a == c * c - b * b == SQUARE_CLASS * h * h
        assert y % (2 * h) == h
        roots = [value * (y // h) for value in (a, b, c)]
        assert all(value % 2 for value in roots)
        i, j, k = [(value - 1) // 2 for value in roots]
        assert 0 <= i < j < k < n
        edges = (triangular(j) - triangular(i), triangular(k) - triangular(j),
                 perimeter - triangular(k) + triangular(i))
        assert all(3 * edge == perimeter for edge in edges)
        folds.add((i, j, k))
    assert len(folds) == 3
    return n


if __name__ == "__main__":
    modulus = lcm(*(row[0] for row in CERTIFICATE))
    assert modulus == 8004348
    assert pell_power(45)[1] % (2 * modulus) == modulus
    first = check(45)
    print(f"The exponent-45 witness uses {len(str(first))} digits for n.\nn = {first}")
    for exponent in (135, 225):
        check(exponent)
    print("The three original rod-arc sums agree at each of the tested exponents.")
