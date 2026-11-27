"""Supplementary exact checks; the unbounded proof is the Lean development.

Uses only the Python standard library. No floating-point arithmetic is used.
"""
from fractions import Fraction as F
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent


def q(n):
    return F(n * (n - 1) * (3 * n * n - 3 * n + 2), 3)


def term(n):
    if n == 1:
        return 1
    if n == 2:
        return 6
    return q(n).__floor__()


def literal_mean(n):
    low, high = (n - 1) ** 4 + 1, n ** 4
    reciprocal_sum = sum((F(1, k) for k in range(low, high + 1)), F(0))
    return F(high - low + 1) / reciprocal_sum


def polynomial(coefficients, t):
    result = 0
    for coefficient in reversed(coefficients):
        result = result * t + coefficient
    return result


def main():
    source_terms = []
    for line in (ROOT / 'sources/A227013.seq').read_text().splitlines():
        if line.startswith(('%S ', '%T ', '%U ')):
            source_terms.extend(int(x) for x in line.split(' ', 2)[2].split(',') if x)
    assert source_terms == [term(n) for n in range(1, len(source_terms) + 1)]

    literal = []
    for n in range(1, 11):
        mean = literal_mean(n)
        assert mean.__floor__() == term(n)
        if n >= 5:
            assert q(n) < mean < q(n) + F(2, 3)
        literal.append({'n': n, 'literal_floor': mean.__floor__()})

    for d in range(1, 51):
        positions = [F(j) - F(d - 1, 2) for j in range(d)]
        assert sum(t ** 2 for t in positions) == F(d * (d * d - 1), 12)
        assert sum(t ** 4 for t in positions) == F(d * (d * d - 1) * (3 * d * d - 7), 240)
        assert sum(t ** 6 for t in positions) == F(d * (d * d - 1) * (3 * d ** 4 - 18 * d * d + 31), 1344)

    cert = json.loads((ROOT / 'polynomial_certificates.json').read_text())
    assert len(cert['P']) == 25 and len(cert['R']) == 15
    assert all(c > 0 for c in cert['P'] + cert['R'])
    for t in range(26):
        n = t + 5
        d, c = n ** 4 - (n - 1) ** 4, (n * n - n + 1) ** 2
        r = F(d - 1, 2)
        v2, v4 = F(d * d - 1, 12), F((d * d - 1) * (3 * d * d - 7), 240)
        v6 = F((d * d - 1) * (3 * d ** 4 - 18 * d * d + 31), 1344)
        lower = F(1, c) + v2 / c ** 3 + v4 / c ** 5 + v6 / c ** 7
        upper = F(1, c) + v2 / c ** 3 + v4 / (c ** 3 * (c * c - r * r))
        assert (q(n) + F(2, 3)) * lower - 1 == F(polynomial(cert['P'], t), 315 * (t * t + 9 * t + 21) ** 14)
        assert 1 - q(n) * upper == F(polynomial(cert['R'], t), 45 * (t + 5) ** 2 * (t * t + 9 * t + 21) ** 6 * ((t + 4) ** 4 + 1))

    den = [1, -4, 6, -5, 5, -6, 4, -1]
    num = [1, 2, 22, 23, 20, 4, -2, 3, -1]
    for degree in range(201):
        coefficient = sum(den[k] * term(degree - k + 1) for k in range(min(degree, 7) + 1))
        assert coefficient == (num[degree] if degree < len(num) else 0)
    for n in range(10, 301):
        assert sum(den[k] * term(n - k) for k in range(8)) == 0
    failure = sum(den[k] * term(9 - k) for k in range(8))
    assert failure == -1

    record = {
        'status': 'PASS',
        'arithmetic': 'exact integers and fractions only',
        'literal_harmonic_blocks': literal,
        'displayed_source_terms': len(source_terms),
        'central_moment_block_lengths': '1..50',
        'polynomial_certificate_replays': 't=0..25; all 40 coefficients positive',
        'generating_function_coefficients': 'degrees 0..200',
        'recurrence_newest_indices': '10..300',
        'recurrence_residual_at_nine': failure,
        'scope': 'Finite supplementary checks; universal identities are proved in Lean.'
    }
    text = json.dumps(record, indent=2) + '\n'
    (ROOT / 'verification_python.json').write_text(text)
    print(text)


if __name__ == '__main__':
    main()
