#!/usr/bin/env python3
"""Exact finite replay supplementary to the unbounded Lean proofs.

Uses only the Python standard library. Source terms and hashes are read from
the immutable snapshots in sources/. Finite checks do not replace the proof.
"""
from collections import Counter
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def closed3(n):
    return 1 + 2 * ((2 * n * n + 2 * n) // 3)


def closed4(n):
    numerator = 22 * n**3 + 33 * n**2 + 26 * n + (12 if n % 2 == 0 else 3)
    assert numerator % 12 == 0, ("nonintegral quadruple formula", n)
    return numerator // 12


def literal_triples(n):
    count = 0
    for a in range(-n, n + 1):
        for b in range(-n, n + 1):
            c = -a - b
            if -n <= c <= n and -n <= b - a <= n and -n <= c - b <= n:
                count += 1
    return count


def literal_quadruples_by_middle_sum(n):
    counts = Counter()
    for a in range(-n, n + 1):
        for b in range(-n, n + 1):
            if not -n <= b - a <= n:
                continue
            for c in range(-n, n + 1):
                d = -a - b - c
                if (-n <= d <= n and -n <= c - b <= n
                        and -n <= d - c <= n):
                    counts[b + c] += 1
    return counts


def slice_formula(n, m):
    h, epsilon = divmod(m, 2)
    return (n + 1 - epsilon) * (2 * m + 1) - h * (h + 1)


def source_terms(sequence_id):
    parts = []
    for line in (ROOT / "sources" / f"{sequence_id}.seq").read_text().splitlines():
        if line.startswith((f"%S {sequence_id} ", f"%T {sequence_id} ",
                            f"%U {sequence_id} ")):
            parts.extend(int(x) for x in line.split(" ", 2)[2].split(",") if x)
    return parts


def main():
    manifest = json.loads((ROOT / "sources" / "manifest.json").read_text())
    for item in manifest:
        data = (ROOT / "sources" / f"{item['id']}.seq").read_bytes()
        assert len(data) == item["bytes"], ("source byte count", item["id"])
        assert hashlib.sha256(data).hexdigest() == item["sha256"], item["id"]

    terms3, terms4 = source_terms("A202253"), source_terms("A202254")
    assert len(terms3) == 49 and len(terms4) == 39
    assert terms3 == [closed3(n) for n in range(1, len(terms3) + 1)]
    assert terms4 == [closed4(n) for n in range(1, len(terms4) + 1)]

    for n in range(51):
        assert literal_triples(n) == closed3(n), ("triple count", n)

    slice_checks = 0
    for n in range(19):
        counts = literal_quadruples_by_middle_sum(n)
        assert sum(counts.values()) == closed4(n), ("quadruple count", n)
        assert all(-n <= s <= n for s in counts), ("middle sum bound", n)
        assert all(counts[s] == counts[-s] for s in range(n + 1)), ("negation", n)
        for s in range(n + 1):
            assert counts[s] == slice_formula(n, n - s), ("quadruple slice", n, s)
            slice_checks += 1
    assert slice_checks == 190

    for n in range(500):
        total = slice_formula(n, n) + 2 * sum(slice_formula(n, m) for m in range(n))
        assert total == closed4(n), ("slice sum", n)

    natural3 = [closed3(n) for n in range(1000)]
    natural4 = [closed4(n) for n in range(1000)]
    assert natural3[0] == natural4[0] == 1
    for n in range(5, 1000):
        assert natural3[n] == (2 * natural3[n - 1] - natural3[n - 2]
                               + natural3[n - 3] - 2 * natural3[n - 4]
                               + natural3[n - 5]), ("triple recurrence", n)
        assert natural4[n] == (3 * natural4[n - 1] - 2 * natural4[n - 2]
                               - 2 * natural4[n - 3] + 3 * natural4[n - 4]
                               - natural4[n - 5]), ("quadruple recurrence", n)

    # Source generating functions begin at n=1; their constant coefficient is 0.
    series3, series4 = [0] + natural3[1:], [0] + natural4[1:]
    for name, series, denominator, numerator in [
        ("triple GF", series3, [1, -2, 1, -1, 2, -1], [0, 3, 3, 2, -1, 1]),
        ("quadruple GF", series4, [1, -3, 2, 2, -3, 1], [0, 7, 10, 2, 4, -1]),
    ]:
        for n in range(1000):
            coefficient = sum(d * series[n - k] for k, d in enumerate(denominator)
                              if k <= n)
            target = numerator[n] if n < len(numerator) else 0
            assert coefficient == target, (name, n, coefficient, target)

    print(json.dumps({
        "status": "PASS",
        "method": "exact Python integer arithmetic; supplementary finite replay",
        "source_hashes": len(manifest),
        "frozen_A202253_terms": len(terms3),
        "frozen_A202254_terms": len(terms4),
        "literal_triples_n": [0, 50],
        "literal_quadruples_n": [0, 18],
        "nonnegative_middle_sum_slices": slice_checks,
        "slice_sum_formula_n": [0, 499],
        "natural_extension_recurrence_n": [5, 999],
        "source_GF_product_coefficients_n": [0, 999],
        "natural_count_constant": 1,
        "source_GF_constant": 0,
    }, indent=2))


if __name__ == "__main__":
    main()
