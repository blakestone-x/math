"""Check the signed Hecke coding against the square's arithmetic map over Q."""
from fractions import Fraction as F
from itertools import product


def multiply(left, right):
    a, b, c, d = left
    e, f, g, h = right
    return a*e+b*g, a*f+b*h, c*e+d*g, c*f+d*h


def act(matrix, point):
    a, b, c, d = matrix
    return (a*point+b)/(c*point+d)


def distance_to_integer(value):
    floor = value.numerator // value.denominator
    return min(value-floor, floor+1-value)


def check_word(ratio_root, digits):
    # ratio_root^2 is the ratio of the smaller to the larger slope magnitude.
    w = ratio_root + 1/ratio_root
    sqrt_t = 1/w
    t = sqrt_t**2
    ell = ratio_root * sqrt_t
    terminal = ratio_root / 7
    hecke = (F(1), F(0), F(0), F(1))
    for digit in digits:
        hecke = multiply(hecke, (F(0), F(-1), F(1), digit*w))
    z = act(hecke, terminal)
    x = sqrt_t * abs(z)
    assert 0 < x < ell

    for digit in digits:
        next_z = -1/z-digit*w
        assert sqrt_t * abs(next_z) == distance_to_integer(t/x)
        nearest = (t/x+F(1, 2)) // 1
        assert nearest == abs(digit)
        sign = 1 if digit * next_z > 0 else -1
        assert x == t/(abs(digit) + sign*sqrt_t*abs(next_z))
        z = next_z
        x = sqrt_t*abs(z)
    assert z == terminal
    return len(digits)


def main():
    counts = steps = 0
    for ratio in (F(1, 8), F(1, 2), F(2, 3), F(7, 8), F(15, 16)):
        for depth in range(1, 5):
            for digits in product((-5, -2, -1, 1, 2, 5), repeat=depth):
                steps += check_word(ratio, digits)
                counts += 1
    print(f'Compared {counts} signed Hecke matrix words with chess inverse itineraries.')
    print(f'All {steps} recovered nearest digits and unsigned remainders agree exactly.')


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run with assertions enabled.')
    main()
