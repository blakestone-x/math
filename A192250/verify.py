"""Supplementary finite checks of the literal source reduction and indexing.

The unbounded result is proved in Lean; this script is not used by Lean.
Uses only Python's standard library.
"""
from pathlib import Path
from math import comb
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parent


def trim(p):
    while p and p[-1] == 0:
        p.pop()
    return p


def reduce_source(p):
    """Write p=X²t+r, substitute (X+1)t+r, and repeat."""
    p = trim(list(p))
    while len(p) > 2:
        previous_degree = len(p) - 1
        t, r = p[2:], p[:2]
        next_p = [0] * max(len(t) + 1, 2)
        for k, value in enumerate(t):
            next_p[k] += value
            next_p[k + 1] += value
        for k, value in enumerate(r):
            next_p[k] += value
        p = trim(next_p)
        assert len(p) - 1 < previous_degree
    return tuple((p + [0, 0])[:2])


def source_terms(identifier):
    text = (ROOT / 'sources' / (identifier + '.seq')).read_text()
    lines = [line.split(' ', 2)[2] for line in text.splitlines()
             if re.match(r'^%[STU] ' + identifier + r' ', line)]
    return [int(x) for x in ''.join(lines).split(',') if x]


def residual(y, n):
    return ((n - 1) * (n - 2) * y[n]
            - (5 * n - 7) * (n - 2) * y[n - 1]
            - 2 * (2 * n - 3) * (3 * n - 8) * y[n - 2]
            + 4 * (2 * n - 3) * (2 * n - 5) * y[n - 3])


def main():
    manifest = json.loads((ROOT / 'sources/manifest.json').read_text())
    for source in manifest['sources']:
        raw = (ROOT / 'sources' / (source['id'] + '.seq')).read_bytes()
        assert hashlib.sha256(raw).hexdigest() == source['sha256']
    pairs = {n: reduce_source([comb(2*k, k) for k in range(n)])
             for n in range(1, 104)}
    for column, identifier in enumerate(['A192250', 'A192251']):
        y = {n: pair[column] for n, pair in pairs.items()}
        expected = source_terms(identifier)
        assert [y[n] for n in range(1, len(expected) + 1)] == expected
        assert all(residual(y, n) == 0 for n in range(4, 104))
        print(f'{identifier}: {len(expected)} published terms match; '
              '100 recurrence instances n=4..103 vanish.')
    print('Literal source substitution terminates for every checked input; '
          'all three source SHA-256 checks pass.')


if __name__ == '__main__':
    main()
