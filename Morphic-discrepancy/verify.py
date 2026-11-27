"""Exact Bellman certificates and a separate check of the one-based positions.

Run with SymPy 1.14.0. No floating-point comparison enters any certificate.
"""
from math import lcm
from sympy import Integer, expand, radsimp, sqrt, sympify


def quadratic(value, d):
    """Return integer A,B,C with value = (A+B*sqrt(d))/C and C positive."""
    radical = sqrt(d)
    value = expand(radsimp(sympify(value)))
    b = value.coeff(radical)
    a = expand(value - b * radical)
    assert a.is_Rational and b.is_Rational, (a, b)
    denominator = lcm(int(a.q), int(b.q))
    return int(a * denominator), int(b * denominator), denominator


def sign(a, b, d):
    """Sign of A+B*sqrt(d) using only integers."""
    def sgn(x):
        return (x > 0) - (x < 0)
    if not a or not b or sgn(a) == sgn(b):
        return sgn(a) or sgn(b)
    return sgn(a) * sgn(a * a - d * b * b)



def verify(name, d, images, seed, h, mu, endpoints, predicted, sample):
    def field_sign(value):
        a, b, _ = quadratic(value, d)
        return sign(a, b, d)

    lows, highs = endpoints[:2], endpoints[2:]
    edges = [[], []]
    for source, word in enumerate(images):
        offset = Integer(0)
        for letter in map(int, word):
            edges[letter].append((source, offset))
            offset += h if letter == 0 else -1
        assert field_sign(offset - mu * (h if source == 0 else -1)) == 0
    assert field_sign(1 - mu) > 0 and field_sign(1 + mu) > 0
    witnesses = []
    for values, minimize in ((lows, True), (highs, False)):
        use = (lows if minimize else highs) if field_sign(mu) > 0 else (highs if minimize else lows)
        for letter in range(2):
            differences = [field_sign(offset + mu * use[a] - values[letter])
                           for a, offset in edges[letter]]
            oriented = differences if minimize else [-x for x in differences]
            assert all(x >= 0 for x in oriented)
            witnesses.append(differences.index(0) + 1)
    result = [lows[0] + h, highs[0] + h, (1 - highs[1])/h, (1 - lows[1])/h]
    assert all(field_sign(a - b) == 0 for a, b in zip(result, predicted))

    word = str(seed)
    while len(word) < 65536:
        word = "".join(images[int(c)] for c in word)
    prefix = word[:65536]
    positions = [[i for i, c in enumerate(prefix, 1) if c == str(a)] for a in range(2)]
    for letter, (observed, reference) in enumerate(zip(positions, sample)):
        assert observed[:len(reference)] == reference
        a, b, c = quadratic(1 + (h if letter == 0 else 1/h), d)
        for side in (0, 1):
            e, f, g = quadratic(predicted[2 * letter + side], d)
            orientation = 1 if side == 0 else -1
            for n, pos in enumerate(observed, 1):
                diff = sign((n*a - pos*c)*g - c*e, n*b*g - c*f, d)
                assert orientation * diff >= 0
                if name == "A284893" and letter == 1:
                    assert diff != 0
    print(f"PASS {name}: exact scale, all edge inequalities, witnesses {tuple(witnesses)}, "
          "four sharp endpoints and 65,536 positions")


def main():
    s = sqrt(2)
    verify("A284893", 2, ("01", "0111"), 0, 1+s, 2-s,
           [0, 1, 2+s, 3+2*s], [1+s, 3+2*s, -2, 0],
           ([1, 3, 7, 9, 13, 17, 21, 23], [2, 4, 5, 6, 8, 10, 11, 12]))
    s = sqrt(3)
    verify("A284901", 3, ("01", "1000"), 0, s/3, 1-s,
           [(-4-3*s)/3, (-1-3*s)/3, (5+s)/3, (5+2*s)/3],
           [(-4-2*s)/3, (5+2*s)/3, (-6-2*s)/3, (9+4*s)/3],
           ([1, 4, 5, 6, 8, 9, 10, 11], [2, 3, 7, 12, 14, 16, 17, 22]))
    s = sqrt(17)
    verify("A285668", 17, ("11", "1101"), 1, (3+s)/2, (3-s)/2,
           [(-31-7*s)/16, (-15-7*s)/16, (5-3*s)/16, (29+5*s)/16],
           [(-7+s)/16, (29+5*s)/16, (-23+s)/32, (13+5*s)/32],
           ([3, 7, 13, 17, 21, 27, 31, 35], [1, 2, 4, 5, 6, 8, 9, 10]))


if __name__ == "__main__":
    main()
