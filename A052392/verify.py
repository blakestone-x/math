#!/usr/bin/env python3
"""Exact finite transcription checks; the unbounded proof is in Lean."""
from pathlib import Path
import json

N = 106
T = [[0] * (r + 1) for r in range(2 * N + 2)]
for r, row in enumerate(T):
    row[0] = row[r] = 1
    for k in range(1, r):
        row[k] = 3 if (r, k) == (2, 1) else (
            T[r - 1][k - 1] + 2 * T[r - 2][k - 1] + T[r - 1][k])
a = [T[2 * n + 1][n] for n in range(N)]
D = [[1] * (N + 1) for _ in range(N + 1)]
for m in range(1, N + 1):
    for n in range(1, N + 1):
        D[m][n] = D[m - 1][n] + D[m][n - 1] + 2 * D[m - 1][n - 1]
d = [D[n][n] for n in range(N + 1)]

snapshot = Path(__file__).with_name('sources').joinpath('A052392.seq').read_text()
expected = []
for line in snapshot.splitlines():
    if line[:2] in ('%S', '%T', '%U'):
        expected.extend(int(x) for x in line.split(' ', 2)[2].split(',') if x)
assert len(expected) == 23
assert a[:len(expected)] == expected

for n in range(100):
    assert (8 * n * a[n] - (32 + 28 * n) * a[n + 1]
            + (78 + 30 * n) * a[n + 2] - (45 + 11 * n) * a[n + 3]
            + (5 + n) * a[n + 4]) == 0

sq = [sum(d[k] * d[n-k] for k in range(n+1)) for n in range(101)]
for n in range(101):
    assert sq[n] - (8 * sq[n-1] if n >= 1 else 0) + (4 * sq[n-2] if n >= 2 else 0) == (n == 0)
    lhs = 2 * a[n-1] if n >= 1 else 0
    rhs = d[n] - (3*d[n-1] if n >= 1 else 0) + (2*d[n-2] if n >= 2 else 0) - (n == 0) + (n == 1)
    assert lhs == rhs

print(json.dumps({
    'source_terms_checked': len(expected),
    'recurrence_indices_checked': [0, 99],
    'formal_identity_coefficients_checked': [0, 100],
    'result': 'PASS',
    'role': 'supplemental finite transcription check, not the proof'
}, indent=2))
