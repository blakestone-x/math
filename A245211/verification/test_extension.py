"""Compare every longest-gap decision with independent explicit cycles for small r."""

import json
import tempfile
from math import gcd, prod
from direct_check import assignments
from replay_extension import ROOT, build, run_range

MODULI = (3, 5, 11, 13, 19, 29, 37, 53, 59, 61, 67, 83)


def explicit_gaps(r, factors):
    passed = set()
    for cs in assignments(r, factors):
        # Count the unit runs directly, including any run crossing the origin.
        nonunits = [i for i, c in enumerate(cs) if c != 1]
        gaps = [
            (nonunits[(j + 1) % len(nonunits)] - i - 1) % r
            for j, i in enumerate(nonunits)
        ]
        longest = max(gaps)
        if longest in passed:
            continue
        m = prod(q for q in MODULI if q - 2 <= longest and q < 2**r - 1)
        # Compute each individual entry with the closed formula.
        valid = True
        for i in range(r):
            coeff = cs[i:] + cs[:i]
            p = sum((1 << (r - j - 1)) * prod(coeff[:j]) for j in range(r))
            if gcd(p, m) != 1:
                valid = False
                break
        if valid:
            passed.add(longest)
    return passed


def main():
    assert all(len({pow(2, j, h) for j in range(h - 1)}) == h - 1 for h in MODULI)
    data = json.loads((ROOT / "factors.json").read_text())["orders"]
    total = positives = 0
    with tempfile.TemporaryDirectory() as tmp:
        exe = build(tmp)
        for r in (2, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25):
            fs = data[str(r)]
            expected = explicit_gaps(r, fs)
            atoms = [q for q, e in fs for _ in range(e)]
            actual = {L for L in range(r) if run_range(exe, r, atoms, L, L)[0] != -1}
            assert actual == expected, (r, actual, expected)
            total += r
            positives += len(actual)
    print(
        total, "longest-gap decisions agree, including", positives, "positive controls."
    )


if __name__ == "__main__":
    main()
