"""Reproduce the polynomial table and the finite certificates in the manuscript."""
import argparse
import json
import subprocess
from collections import Counter
from fractions import Fraction
from itertools import combinations, permutations
from math import comb, factorial
from pathlib import Path

from enumerate_321 import clusters, coefficient, records

HERE = Path(__file__).resolve().parent
# Numerators printed by Nakamura and Zeilberger, in descending powers of n.
NZ = {
    5: [26246, 136646, -115872, 22524, -9648450, 71304534, 381205612,
        1607633896, 2800103664, 3611692800, -32891443200],
    6: [193311, 2349954, 13035003, 95151030, 406430793, 2889552582,
        14335663329, 60005854890, 313010684796, 1025692693464,
        1283595375168, -6909513045120, -28177269120000],
    7: [1386032, 13111080, 22526480, 355187760, -1654450096, 10534951680,
        15797223760, -305671694640, 3750695521216, -26631101348520,
        -86395090065440, -636425872408320, 3647384624274048, 11386434230674560,
        103032675524966400, -157858417817856000, -763734137886720000],
}


def value(poly, n):
    result = 0
    for c in poly:
        result = result * n + c
    return result


def count(data, r, n):
    return coefficient(r, data[r]["P"], data[r]["Q"], n)


def normalized(data, r, n):
    return Fraction(count(data, r, n) * factorial(n+2*r+1) * factorial(n-r),
                    factorial(2*n-r))


def published_formulas(data):
    for r, poly in NZ.items():
        # For every Catalan shift j = 2r-i in these rows, 2j+r >= 0.
        # Multiplying the normalized formula by the product of (n+k) for
        # -r+1 <= k <= 2r clears its denominators and gives degree <= 5r.
        # The same is true for NZ's expression. 5r+1 evaluations certify equality.
        assert 2*(2*r - (len(data[r]["Q"])-1)) + r >= 0
        for n in range(r, 6*r+1):
            denominator = (n-5)*(n-6) if r == 7 else 1
            assert normalized(data, r, n) == Fraction(value(poly, n), denominator)
    assert value(NZ[7], 5) == 1621934672117760000
    assert value(NZ[7], 6) == 13624251245789184000
    assert count(data, 7, 28) == 105460690841118844
    assert normalized(data, 7, 28) == Fraction(12308472573908433737278464000, 23)
    assert len(data[8]["P"]) == 22 and data[8]["P"][-1] == 4
    assert len(data[8]["Q"]) == 21
    exact_difference = sum((-1)**(15-k)*comb(15,k)*normalized(data, 7, k+7)
                           for k in range(16))
    assert exact_difference == -845552707743744000
    exact_moment = sum((-1)**(21-k)*comb(21+k,21-k)*count(data, 8, k+4)
                       for k in range(22))
    assert exact_moment == -2


def check_permutations(data):
    for n in range(10):
        triples = list(combinations(range(n), 3))
        hist = Counter(sum(perm[i] > perm[j] > perm[k] for i,j,k in triples)
                       for perm in permutations(range(n)))
        for r in range(len(data)):
            assert hist[r] == count(data, r, n)


def growth_certificate():
    k = 10
    y = Fraction(100, 319)
    transfer = [[Fraction(0)] * (k+1) for _ in range(k+1)]
    for (c, a, b, length), multiplicity in clusters(k).items():
        weight = multiplicity*y**c / 4**length
        for h, row in enumerate(transfer):
            row[b] += (2+4*min(h,a)) * weight
    vec = [1] * (k+1)
    for _ in range(4):
        previous = vec
        vec = [sum(x*w for x,w in zip(row, previous)) for row in transfer]
    assert all(before > 0 and after * 125000 > before * 125001
               for before, after in zip(previous, vec))


def check_subsets(program, data):
    raw = subprocess.check_output([str(Path(program).resolve())], text=True)
    rows = [list(map(int, line.split())) for line in raw.splitlines()]
    assert len(rows) == 26
    prime = 47
    for n, row in enumerate(rows):
        assert row == [n] + [count(data,r,n) % prime for r in range(9)]
    moment = sum((-1)**(21-k)*comb(21+k,21-k)*rows[k+4][9] for k in range(22))
    difference = sum((-1)**(15-k)*comb(15,k)*rows[k+7][8]
                     * factorial(k+22)*factorial(k)*pow(factorial(2*k+7),-1,prime)
                     for k in range(16))
    assert (moment % prime, difference % prime) == (45, 5)
    print("The separate subset count confirms both contradictions modulo 47.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--subsets", metavar="EXECUTABLE", help="run the compiled subset_check.cpp")
    args = parser.parse_args()
    data = records(18)
    assert data == json.loads((HERE/"polynomials.json").read_text())
    for entry in data:
        r, p, q = entry["r"], entry["P"], entry["Q"]
        assert (p[0], q[0]) == (1, -1)
        amplitude = -4**(2*r)*sum(Fraction(c,4**i) for i,c in enumerate(q))
        assert amplitude == Fraction(entry["amplitude"])
    check_permutations(data)
    published_formulas(data)
    growth_certificate()
    print("19 polynomial pairs, all permutations through length 9, and the three NZ identities passed.")
    print("The factorial and degree counterexamples and the strict growth bound 3.19 passed.")
    if args.subsets:
        check_subsets(args.subsets, data)
