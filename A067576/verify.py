#!/usr/bin/env python3
"""Supplementary integer replay; all unbounded assertions are proved in Lean."""
from hashlib import sha256
import json
from pathlib import Path
import re


def row_prefix(weight: int, length: int) -> list[int]:
    """Successive binary words of a fixed weight, by the bit-successor algorithm."""
    n = (1 << weight) - 1
    result = []
    for _ in range(length):
        result.append(n)
        low_bit = n & -n
        shifted = n + low_bit
        n = shifted | (((shifted ^ n) >> 2) // low_bit)
    assert all(n.bit_count() == weight for n in result)
    assert all(a < b for a, b in zip(result, result[1:]))
    return result


def main() -> None:
    here = Path(__file__).resolve().parent
    bound = 80
    rows = {i: row_prefix(i, bound) for i in range(1, bound + 1)}

    # Direct enumeration validates the independent successor implementation.
    brute = {i: [] for i in range(1, 17)}
    for n in range(1, 1 << 16):
        brute[n.bit_count()].append(n)
    for i, entries in brute.items():
        length = min(len(entries), bound)
        assert rows[i][:length] == entries[:length]

    source = (here / 'sources/A067576.seq').read_text()
    terms = []
    for line in source.splitlines():
        if re.match(r'%[STU] A067576 ', line):
            terms.extend(int(v) for v in line.split(' ', 2)[2].split(',') if v)
    antidiagonals = []
    for total in range(2, 20):
        antidiagonals.extend(rows[i][total-i-1] for i in range(1, total))
    assert terms == antidiagonals[:len(terms)]

    formula_checks = doubling_checks = 0
    for i in range(1, bound + 1):
        for j in range(1, bound + 1):
            if i >= j-1:
                assert rows[i][j-1]+1 == ((1 << j)-1)*(1 << (i+1-j))
                formula_checks += 1
            if i < bound and i >= max(1, j-1):
                assert rows[i+1][j-1]+1 == 2*(rows[i][j-1]+1)
                doubling_checks += 1
    for j in range(3, bound+1):
        assert rows[j-2][j-1]+1 == 5*(1 << (j-3))
        assert rows[j-1][j-1]+1 == (1 << j)-1
        assert rows[j-1][j-1]+1 != 2*(rows[j-2][j-1]+1)

    result = {
        'status': 'passed',
        'method': 'independent fixed-popcount successor enumeration, validated against direct enumeration below 2^16',
        'rows': [1, bound],
        'columns': [1, bound],
        'source_antidiagonal_terms': len(terms),
        'closed_form_checks': formula_checks,
        'doubling_checks': doubling_checks,
        'sharpness_counterexamples': bound-2,
        'source_sha256': sha256((here/'sources/A067576.seq').read_bytes()).hexdigest(),
        'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
        'scope': 'Finite independent replay only; the unbounded source theorem and minimality are kernel-checked in Lean.'
    }
    text = json.dumps(result, indent=2)+'\n'
    (here/'verification_python.json').write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
