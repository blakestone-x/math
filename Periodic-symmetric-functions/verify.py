"""Check Mathar's periodic elementary-symmetric functions using integer arithmetic."""

import argparse
from itertools import combinations
from math import prod
from pathlib import Path


# Coefficients in increasing order, after removing the factor x, from the OEIS proposals.
PREDICTIONS = (
    ('A203164', (4, 1, 2, 3), (1, 5, 14, 50, 176, 80, 64)),
    ('A203165', (3, 4, 1, 2), (1, 7, 19, 50, 126, 432, 144)),
    ('A203166', (1, 2, 3, 4, 5), (1, 3, 11, 50, 274, 154, 188, 324, 576)),
    ('A203167', (2, 2, 1), (1, 4, 8, 12, 16)),
    ('A203230', (1, 3), (1, 4, 1)),
    ('A203231', (3, 1), (1, 4, 9)),
    ('A203232', (2, 3), (1, 5, 4)),
    ('A203233', (3, 2), (1, 5, 9)),  # Robert Israel's previously verified case
    ('A203234', (1, 1, 1, 2), (1, 2, 3, 7, 5, 3, 1)),
    ('A203235', (1, 1, 1, 3), (1, 2, 3, 10, 7, 4, 1)),
)


def prefix_coeffs(period, limit, degree):
    coeff = (1,) + (0,) * degree
    rows = [coeff]
    for i in range(limit):
        x = period[i % len(period)]
        coeff = (x * coeff[0],) + tuple(x * coeff[r] + coeff[r-1] for r in range(1, degree+1))
        rows.append(coeff)
    return rows


def check(source):
    count = 0
    for aid, period, predicted in PREDICTIONS:
        d, P = len(period), prod(period)
        table = prefix_coeffs(period, 100, 6)
        for n in range(11):
            values = (period * (n // d + 1))[:n]
            for r in range(min(n, 6) + 1):
                assert table[n][r] == sum(prod(z) for z in combinations(values, n-r))

        a = [row[1] for row in table]
        numerator = [a[n] - (2*P*a[n-d] if n >= d else 0)
                     + (P**2*a[n-2*d] if n >= 2*d else 0) for n in range(len(a))]
        assert numerator[:2*d] == [0, *predicted], aid
        assert not any(numerator[2*d:]), aid

        for r in range(7):
            v = [row[r] for row in table]
            for _ in range(r):
                v = [b - P*a for a, b in zip(v, v[d:])]
            assert any(v)
            assert all(b == P*a for a, b in zip(v, v[d:]))

        if source:
            lines = (source / 'seq' / aid[:4] / (aid + '.seq')).read_text().splitlines()
            listed = [int(x) for line in lines if line[:2] in ('%S', '%T', '%U')
                      for x in line.split(maxsplit=2)[2].split(',') if x]
            assert listed == a[1:len(listed)+1], aid
            count += len(listed)
        print(f'{aid}: period {period}, first-omission order {2*d}, numerator agrees')
    print('All 10 identities and omission counts 0 through 6 were checked.')
    if source:
        print(f'All {count} source sequence terms agree.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--oeis-repo', type=Path, help='checkout of oeis/oeisdata')
    check(parser.parse_args().oeis_repo)
