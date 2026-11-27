"""Replay the additional squarefree counts with checked prime factorizations.
Run in the verification archive root. Requires g++, GMP, and Python 3.9+.
"""

import argparse
import json
import os
import subprocess
import tempfile
from math import prod
from pathlib import Path
from squarefree import check_prime

ROOT = Path(__file__).resolve().parent


def build(directory):
    exe = Path(directory) / "gap_cycle"
    subprocess.run(
        [
            "g++",
            "-std=c++17",
            "-O2",
            "-Wall",
            "-Wextra",
            str(ROOT / "gap_cycle.cpp"),
            "-lgmpxx",
            "-lgmp",
            "-o",
            str(exe),
        ],
        check=True,
    )
    return exe


def run_range(exe, r, atoms, lo, hi):
    env = dict(os.environ, A245_MIN_GAP=str(lo), A245_MAX_GAP=str(hi))
    line = subprocess.check_output(
        [str(exe), str(r), *map(str, atoms)], env=env, text=True
    )
    rank, gap, states = map(int, line.split())
    assert rank == r
    return gap, states


def validate(data, r):
    fs = data["factors"]
    assert all(isinstance(q, int) and q >= 2 and e > 0 for q, e in fs)
    assert len({q for q, e in fs}) == len(fs)
    assert prod(q**e for q, e in fs) == 2**r + 1
    proven = set()
    for q, e in fs:
        check_prime(q, data["certificates"], proven)
    return [q for q, e in fs for _ in range(e)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("r", nargs="*", type=int)
    args = parser.parse_args()
    data = json.loads((ROOT / "extended-factors.json").read_text())

    def odd_prime_power(n):
        from math import isqrt

        d = next((p for p in range(3, isqrt(n) + 1, 2) if n % p == 0), n)
        while n % d == 0:
            n //= d
        return n == 1

    # The algebraic 7*3^j obstruction settles 189. Every even count >2
    # and every odd prime-power count are settled in Section 2.
    required = [r for r in range(103, 203, 2) if not odd_prime_power(r) and r != 189]
    if sorted(map(int, data)) != required:
        raise RuntimeError("The dataset must cover all remaining counts through 202")
    ranks = args.r or required
    with tempfile.TemporaryDirectory() as directory:
        exe = build(directory)
        for r in ranks:
            atoms = validate(data[str(r)], r)
            # This split lets the two most expensive parts of r=105 be replayed separately.
            intervals = [(0, 50), (51, r - 1)] if r == 105 else [(0, r - 1)]
            for lo, hi in intervals:
                gap, states = run_range(exe, r, atoms, lo, hi)
                print(r, lo, hi, gap, states, flush=True)
                if gap >= 0:
                    raise RuntimeError(
                        f"Unresolved modular cycle at r={r}, longest gap={gap}"
                    )


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run normally so that certificate assertions execute.")
    main()
