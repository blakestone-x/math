"""Verify prefix interlacing and exact common factors with integer polynomials."""
import itertools
from math import comb
from sympy import Poly, symbols

x = symbols("x")


def refined(bounds):
    old = [Poly(1, x)]
    for n in bounds:
        m = len(old)
        new = []
        for j in range(n):
            g = Poly(0, x)
            for i, f in enumerate(old):
                sign = (j * m > i * n) - (j * m < i * n)
                factor = (1 + x) if sign == 0 else (x if sign > 0 else 1)
                g += f * Poly(factor, x)
            new.append(g)
        old = new
    return sum(old[1:], old[0] * Poly(1 + x, x))


def literal(bounds):
    total = [0] * (len(bounds) + 2)
    for seq in itertools.product(*(range(s) for s in bounds)):
        numerators = (0, *seq, 0)
        denominators = (1, *bounds, 1)
        increases = equalities = 0
        for j in range(len(numerators) - 1):
            left = numerators[j] * denominators[j + 1]
            right = numerators[j + 1] * denominators[j]
            increases += left < right
            equalities += left == right
        for k in range(equalities + 1):
            total[increases + k] += comb(equalities, k)
    return Poly.from_list(total[::-1], gens=x)


def check_strict_sturm(larger, smaller):
    """Signed remainders of successive degrees certify interlacing."""
    f, g = larger, smaller
    assert f.degree() == g.degree() + 1
    while g.degree() > 0:
        r = -f.rem(g)
        assert r.degree() == g.degree() - 1 and r.LC() > 0
        f, g = g, r
    assert g.LC() > 0


def main():
    prefixes = {(): Poly(1 + x, x)}
    strict = shared = direct = 0
    for length in range(1, 6):
        for bounds in itertools.product(range(1, 5), repeat=length):
            cur = refined(bounds)
            prefixes[bounds] = cur
            last = prefixes[bounds[:-1]]
            if length <= 4:
                assert cur == literal(bounds)
                direct += 1
            if bounds[-1] == 1:
                assert cur == last * Poly(1 + x, x)
                share = last
            elif 1 in bounds:
                i = max(i for i, s in enumerate(bounds) if s == 1)
                share = prefixes[bounds[:i]]
            else:
                share = Poly(1, x)
            assert last.gcd(cur).monic() == share.monic()
            if 1 in bounds:
                shared += 1
            else:
                strict += 1
            check_strict_sturm(cur.exquo(share), last.exquo(share))
    for size in range(1, 9):
        counts = [0] * (size + 1)
        for perm in itertools.permutations(range(size)):
            fixed = sum(i == j for i, j in enumerate(perm))
            excedances = sum(j > i for i, j in enumerate(perm))
            for k in range(fixed + 1):
                counts[excedances + k] += comb(fixed, k)
        assert refined(tuple(range(2, size + 1))) == Poly.from_list(counts[::-1], gens=x)
    print(f"{strict} strictly interlacing pairs and {shared} pairs with the predicted gcd.")
    print(f"{direct} independent inversion-sequence enumerations; permutations through 8.")


if __name__ == "__main__":
    main()
