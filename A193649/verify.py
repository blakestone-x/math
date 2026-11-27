"""Check ten predictions against the triangular downstep, optionally all OEIS data."""
import argparse
from fractions import Fraction
from math import comb
from pathlib import Path


def fib_coefficient(m, k):
    gap = m - 1 - k
    return 0 if gap < 0 or gap % 2 else comb(m - 1 - gap//2, gap//2)


def kernel(entry, n, k):
    if entry in (658, 659):
        return n + k + (entry == 659)
    if entry == 663:
        return k + 1
    if entry == 665:
        return (n + 1) * (k + 1)
    return 1


def row(entry, n, k):
    if entry == 649:
        return fib_coefficient(n+1, k)
    if entry in (654, 655):
        return ((n+1)*(n+k+2) + (entry == 655)) // 2
    if entry == 656:
        return 2**(n-k) * 5**k
    if entry in (658, 659):
        return comb(n, k)
    if entry == 661:
        return comb(n, k) * (3**(n-k)+1) // 2
    if entry == 662:
        return 2 if n == 0 else fib_coefficient(n+1, k) + fib_coefficient(n-1, k)
    if entry == 663:
        return fib_coefficient(n, k)
    if entry == 665:
        return (n+1)*(k+1)
    raise ValueError(entry)


def direct(entry, length):
    r = [1]
    for n in range(1, length):
        r.append(sum(kernel(entry, n-1, k) * r[n-1-k] for k in range(n)))
    return [sum(row(entry, n, k) * r[n-k] for k in range(n+1)) for n in range(length)]


def mul(a, b):
    out = [0] * (len(a)+len(b)-1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            out[i+j] += ai*bj
    return out


def product(*polys):
    out = [1]
    for poly in polys:
        out = mul(out, poly)
    return out


rounded_den = product([1,1], [1,2], [1,-1], [1,-1], *(([1,-2],)*3))
common_den = product([1,-1], [1,-1,-4])
rational = {
    649: ([1,-1,-2], common_den),
    654: ([1,2,-4,-4,0,8], rounded_den),
    655: ([1,2,-3,-9,8,4], rounded_den),
    656: ([1,-2], product([1,-4], [1,-5])),
    661: ([1,-8,13], product([1,-1], [1,-3], [1,-7])),
    662: ([2,-3,-3,2], common_den),
    663: ([0,1,-1,1], [1,-2,-6,7,1]),
}


def verify(entry, values):
    if entry in rational:
        num, den = rational[entry]
        assert mul(den, values)[:len(values)] == num + [0]*(len(values)-len(num))
    if entry in (654, 655):
        for n, v in enumerate(values):
            average = Fraction((n+1)*((n+3)*2**n-1), 2)
            offset = Fraction(2**n-1, 6) if n % 2 == 0 else 0
            assert v == average + (1 if entry == 655 else -1)*offset
    if entry == 656:
        assert all(v == 3*5**n - 2*4**n for n, v in enumerate(values))
    if entry in (658, 659):
        c = entry - 658
        for n in range(4, len(values)):
            assert (values[n] - (n+4+c)*values[n-1] + (4*n-1+3*c)*values[n-2]
                    + (10-5*n-2*c)*values[n-3] + 2*(n-3)*values[n-4]) == 0
    if entry == 665:
        for n in range(3, len(values)):
            assert values[n] - (n+4)*values[n-1] + (n+1)*values[n-2] - values[n-3] == 0


def source_terms(repo, entry):
    path = repo / "seq" / "A193" / f"A193{entry:03d}.seq"
    fields = [line.split(maxsplit=2)[2] for line in path.read_text().splitlines()
              if line.startswith(("%S ", "%T ", "%U "))]
    return [int(term) for term in "".join(fields).split(",") if term]


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--oeis-repo", type=Path)
    args = parser.parse_args()
    compared = 0
    for entry in (649, 654, 655, 656, 658, 659, 661, 662, 663, 665):
        published = source_terms(args.oeis_repo, entry) if args.oeis_repo else []
        values = direct(entry, max(90, len(published)))
        verify(entry, values)
        assert values[:len(published)] == published
        compared += len(published)
    print("All ten formulas checked against the downstep for 90 terms each.")
    if args.oeis_repo:
        print(f"Matched {compared} terms from the ten source entries.")
