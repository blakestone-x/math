"""Verify the printed coefficient table and enumerate independent partial transversals."""

from collections import Counter
from itertools import combinations, product
from math import comb, factorial, gcd, isqrt, prod
from pathlib import Path

from partitions import coefficients


def printed_coefficients():
    terms = {}
    for line in Path(__file__).with_name('enumeration.md').read_text().splitlines():
        if not line.startswith('| '):
            continue
        cells = [cell.strip() for cell in line.strip('|').split('|')]
        if len(cells) != 3 or not cells[0].isdigit():
            continue
        k = int(cells[0])
        ds = () if cells[1] == '—' else tuple(map(int, cells[1].split(',')))
        for e, value in enumerate(map(int, cells[2].split(',')), start=2):
            if value:
                terms.setdefault(k, {})[e, ds] = value
    return terms


def addition_table(moduli):
    members = list(product(*(range(m) for m in moduli)))
    index = {g: i for i, g in enumerate(members)}
    return [[index[tuple((x+y) % m for x, y, m in zip(a, b, moduli))]
             for b in members] for a in members]


def direct_counts(table):
    # After each row, accumulate counts by the two sets of coordinates used so far.
    n = len(table)
    assert all(set(row) == set(range(n)) for row in (*table, *zip(*table)))
    states = {(0, 0): 1}
    for row in table:
        following = states.copy()  # leave the row empty
        for (columns, symbols), ways in states.items():
            for c, s in enumerate(row):
                cb, sb = 1 << c, 1 << s
                if not (columns & cb or symbols & sb):
                    key = columns | cb, symbols | sb
                    following[key] = following.get(key, 0) + ways
        states = following
    counts = Counter()
    for (columns, _), ways in states.items():
        counts[columns.bit_count()] += ways
    return counts


def check_four(table, counts):
    n = len(table)
    intercalates = sum(table[r][c] == table[s][d] and table[r][d] == table[s][c]
                       for r, s in combinations(range(n), 2)
                       for c, d in combinations(range(n), 2))
    assert 6*counts[3] == n*n*(n-1)*(n-2)*(n*n-6*n+10)
    assert 4*counts[4] == (n*n-9*n+24)*counts[3] - n*n*((n-2)**3+1) + 4*intercalates


def check_polynomials(moduli, counts, printed):
    n = prod(moduli)
    for k, terms in printed.items():
        labeled = sum(a*n**e * prod(gcd(d, m) for d in ds for m in moduli)
                      for (e, ds), a in terms.items())
        assert labeled == factorial(k)*counts[k], (moduli, k, labeled, counts[k])


def is_prime(p):
    return p >= 2 and all(p % d for d in range(2, isqrt(p)+1))


def check_congruences(n, counts):
    for k in range(1, n+1):
        exceptional = k % 2 and is_prime(k) and n % k == 0
        residue = (k-2)*n*n//k if exceptional else 0
        assert (counts[k]-residue) % (n*n) == 0, (n, k, counts[k])
        if n % 3 == 0 or k % 3 == 2:
            assert counts[k] % 3 == 0
        assert counts[k] % 2 == (comb(n, k) % 2 if n % 2 else 0)


if __name__ == '__main__':
    printed = printed_coefficients()
    assert set(printed) == {4, 5, 6, 7}
    for k in printed:
        assert coefficients(k) == printed[k], k
    print('Symbolic partition sums agree with every printed coefficient for k=4,5,6,7.')

    for n in range(1, 11):
        table = addition_table([n])
        counts = direct_counts(table)
        check_congruences(n, counts)
        check_four(table, counts)
        check_polynomials([n], counts, printed)
        if n == 9:
            assert [counts[k] for k in range(n+1)] == [
                1, 81, 2268, 27972, 160866, 423306, 469800, 188568, 18225, 2025]
    for moduli in [(2,2), (2,2,2), (4,2), (3,3)]:
        table = addition_table(moduli)
        counts = direct_counts(table)
        check_four(table, counts)
        check_polynomials(moduli, counts, printed)
    # A Latin square obtained by switching a single intercalate tests the
    # four-piece identity separately from the group-table coefficient formulas.
    table = addition_table([8])
    for r in (0, 4):
        table[r][0], table[r][4] = table[r][4], table[r][0]
    check_four(table, direct_counts(table))
    print('Direct enumeration passed for cyclic orders 1–10, four further abelian tables, and an intercalate switch.')
