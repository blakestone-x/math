#!/usr/bin/env python3
"""Supplementary exact-integer replay; the unbounded proof is in Lean."""

from hashlib import sha256
import json
from pathlib import Path
import re


def from_cubic_definition(n: int, h: int = 4) -> int:
    """Find floor(1/(cuberoot(n^3+h)-n)) without real arithmetic.

    The caller's range ensures n^3 < n^3+h < (n+1)^3. The monotone
    predicate is cuberoot(n^3+h) <= n+1/q, so the largest valid
    integer q is exactly the desired floor. Bounds are found by doubling.
    """
    radicand = n**3 + h
    assert n**3 < radicand < (n + 1) ** 3

    def valid(q: int) -> bool:
        return radicand * q**3 <= (n * q + 1) ** 3

    lo, hi = 1, 2
    assert valid(lo)
    while valid(hi):
        lo, hi = hi, hi * 2
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if valid(mid):
            lo = mid
        else:
            hi = mid
    assert radicand * lo**3 <= (n * lo + 1) ** 3
    assert (n * (lo + 1) + 1) ** 3 < radicand * (lo + 1) ** 3
    return lo


def main() -> None:
    here = Path(__file__).resolve().parent
    limit = 10000
    actual = [0] + [from_cubic_definition(n) for n in range(1, limit + 1)]
    expected = [3 * n * n // 4 + int(n in (1, 3)) for n in range(limit + 1)]
    assert actual == expected

    source_text = (here / "sources/A184534.seq").read_text()
    source_terms = []
    for line in source_text.splitlines():
        if re.match(r"%[STU] A184534 ", line):
            source_terms.extend(int(x) for x in line.split(" ", 2)[2].split(",") if x)
    assert source_terms == actual[1 : len(source_terms) + 1]

    for n in range(8, limit + 1):
        assert actual[n] == 2 * actual[n - 1] - 2 * actual[n - 3] + actual[n - 4]
    assert actual[7] != 2 * actual[6] - 2 * actual[4] + actual[3]

    denominator = [1, -2, 0, 2, -1]
    numerator = [0, 1, 1, 1, 0, -1, 2, -1]
    for n in range(limit + 1):
        coefficient = sum(c * actual[n - k] for k, c in enumerate(denominator) if k <= n)
        assert coefficient == (numerator[n] if n < len(numerator) else 0)

    general_count = 0
    for h in range(1, 41):
        for n in range(h, h + 101):
            assert from_cubic_definition(n, h) == 3 * n * n // h
            general_count += 1

    result = {
        "status": "passed",
        "method": "exact integer cubic comparisons with doubling and binary search; no floating-point roots",
        "source_definition_values": {"n_min": 1, "n_max": limit, "count": limit},
        "source_prefix_count": len(source_terms),
        "recurrence": {"newest_index_min": 8, "newest_index_max": limit},
        "recurrence_failure_at_7": True,
        "generating_function_coefficients": {"min": 0, "max": limit},
        "general_estimate": {"h_min": 1, "h_max": 40, "n_range": "h through h+100 inclusive", "count": general_count},
        "scope": "Finite independent replay only; unbounded conclusions are kernel-checked in the Lean files.",
        "source_sha256": sha256((here / "sources/A184534.seq").read_bytes()).hexdigest(),
        "verifier_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    output = json.dumps(result, indent=2) + "\n"
    (here / "verification_python.json").write_text(output)
    print(output, end="")


if __name__ == "__main__":
    main()
