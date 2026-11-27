"""Exact formulas and independent checks for Jeffery's rhombus coronas (Python 3)."""

import argparse
from itertools import product
from math import comb, prod
from pathlib import Path


def jump_sum(n, b):
    width = n - 1 - b
    return width - comb(width, 2)


def marked_gap(n, b):
    c = n - b
    h = b - 1
    s = jump_sum(n, b)
    return (comb(h + 4, 5) + (2 * c + 3) * comb(h + 3, 4)
            + ((c + 1) * (c + 3) + s) * comb(h + 2, 3)
            + ((c + 1) ** 2 + s) * comb(h + 1, 2))


def corona(n, k):
    """A233332(n,k), with four directed edge positions distinguished."""
    N, ell = n - 1, n - k
    S, T = jump_sum(n, k), jump_sum(n, ell)
    P = N**4 + 2 * N**2 * (S + T) + S**2 + T**2
    numerator = 4**n * P - 2**(n + 1) * (marked_gap(n, k) + marked_gap(n, ell))
    assert numerator % 16 == 0
    return numerator // 16 + n - 2


def core(n, k):
    """A233330(n,k), counting the four tiles along the central edges."""
    N, ell = n - 1, n - k
    U, V = comb(ell - 1, 2), comb(k - 1, 2)
    return N**4 - 2 * N**2 * (U + V) + U**2 + V**2


def reduced_core(n, k):
    """A233331(n,k), identifying isometries of the central tile."""
    N, ell = n - 1, n - k
    U, V = comb(ell - 1, 2), comb(k - 1, 2)
    half = N**2 - U - V
    diag_k = ((n + k) // 2) ** 2 - V
    diag_ell = ((n + ell) // 2) ** 2 - U
    total = core(n, k) + half + diag_k + diag_ell
    if n == 2 * k:
        assert (total + 4 * N) % 8 == 0
        return (total + 4 * N) // 8
    assert total % 4 == 0
    return total // 4


def fillings(n):
    """Bounded compositions, and those invariant under reversal, for each gap."""
    f, pal = [1], [1]
    for s in range(1, 2 * n):
        f.append(sum(f[max(0, s - n + 1):s]))
        # A palindrome either consists of a single part or has equal outer parts.
        pal.append(int(s < n) + sum(pal[s - 2 * a] for a in range(1, min(n - 1, s // 2) + 1)))
    return f, pal


def burnside_sum(n, k, labeled=None):
    """Independently sum the sector-filling counts fixed by each symmetry."""
    N, ell = n - 1, n - k
    f, pal = fillings(n)
    half = sum((N - abs(d)) * f[k + d] * f[ell - d]
               for d in range(max(-k, 1 - N), min(ell, N - 1) + 1))

    def diagonal(b):
        L = (n + b) // 2
        return sum(pal[n + b - 2 * u] * pal[n + b - 2 * w] * f[u + w - b]
                   for u in range(1, L + 1) for w in range(max(1, b - u), L + 1))

    total = (corona(n, k) if labeled is None else labeled) + half + diagonal(k) + diagonal(ell)
    if n == 2 * k:
        total += 2 * N * (f[k] + 2**(n - 2))
        assert total % 8 == 0
        return total // 8
    assert total % 4 == 0
    return total // 4


def diagonal_corona(n, b):
    L, B = (n + b) // 2, b // 2
    X = L**2 - comb(b - 1, 2) + b - 1
    Y = B * (L - b + 2) + comb(B + 1, 2)
    return (2**(n - 1 - (n + b) % 2) * X - 2**(L + B - b) * Y
            + int(b % 2 == 0) - int((n + b) % 2 == 0))


def reduced_corona(n, k):
    """Closed formula for the symmetry classes in the definition of A233333."""
    N = n - 1
    H = N**2 - comb(n - k - 1, 2) - comb(k - 1, 2)
    half = 2**(n - 2) * (H + n - 2) - (n - 2)
    total = corona(n, k) + half + diagonal_corona(n, k) + diagonal_corona(n, n - k)
    if n == 2 * k:
        total += 2 * N * (2**(k - 1) + 2**(n - 2))
        assert total % 8 == 0
        return total // 8
    assert total % 4 == 0
    return total // 4


def direct_counts(n, k):
    N, ell = n - 1, n - k
    f, _ = fillings(n)
    raw_core = raw_corona = 0
    for j in product(range(1, N + 1), repeat=4):
        gaps = (k + j[3] - j[0], ell + j[0] - j[1],
                k + j[1] - j[2], ell + j[2] - j[3])
        if min(gaps) >= 0:
            raw_core += 1
            raw_corona += prod(f[s] for s in gaps)
    return raw_core, raw_corona


def direct_orbits(n, k):
    """Literal orbit representatives for edge labels and four ordered compositions."""
    fparts = [[()]]
    for s in range(1, 2 * n):
        fparts.append([(a,) + tail for a in range(1, min(n - 1, s) + 1)
                       for tail in fparts[s - a]])
    core_reps, corona_reps = set(), set()
    steps = range(4) if n == 2 * k else (0, 2)

    def orbit(j, words):
        for t in steps:
            yield (tuple(j[(i - t) % 4] for i in range(4)),
                   tuple(words[(i - t) % 4] for i in range(4)))
            yield (tuple(n - j[(t - i - 1) % 4] for i in range(4)),
                   tuple(words[(t - i) % 4][::-1] for i in range(4)))

    for j in product(range(1, n), repeat=4):
        gaps = tuple(b + j[i - 1] - j[i] for i, b in enumerate((k, n - k) * 2))
        if min(gaps) < 0:
            continue
        core_reps.add(min(x[0] for x in orbit(j, ((),) * 4)))
        for words in product(*(fparts[s] for s in gaps)):
            corona_reps.add(min(orbit(j, words)))
    return len(core_reps), len(corona_reps)


def matrix_count(n, k):
    """Jeffery's four-gap sum as trace((T_k T_ell)^2)."""
    f, _ = fillings(n)
    indices = range(1, n)
    left_rows = [[f[k + u - v] if k + u >= v else 0 for v in indices] for u in indices]
    right_columns = [[f[n-k + v - w] if n-k + v >= w else 0 for v in indices] for w in indices]
    pair = [[sum(a * b for a, b in zip(row, col)) for col in right_columns] for row in left_rows]
    return sum(pair[i][j] * pair[j][i] for i in range(n-1) for j in range(n-1))


def hankel_determinant(values, size, prime):
    matrix = [[values[i + j] % prime for j in range(size)] for i in range(size)]
    det = 1
    for j in range(size):
        pivot = next((r for r in range(j, size) if matrix[r][j]), None)
        if pivot is None:
            return 0
        if pivot != j:
            matrix[j], matrix[pivot] = matrix[pivot], matrix[j]
            det = -det
        det = det * matrix[j][j] % prime
        inverse = pow(matrix[j][j], -1, prime)
        for r in range(j + 1, size):
            factor = matrix[r][j] * inverse % prime
            for c in range(j + 1, size):
                matrix[r][c] = (matrix[r][c] - factor * matrix[j][c]) % prime
    return det % prime


def check_least_orders():
    prime = 1_000_003
    for k in (1, 2, 3):
        labeled, orbits = [], []
        for n in range(2*k + 1, 2*k + 40):
            count = matrix_count(n, k)
            assert count == corona(n, k)
            labeled.append(count)
            orbit_count = burnside_sum(n, k, labeled=count)
            assert orbit_count == reduced_corona(n, k)
            orbits.append(orbit_count)
        residues = hankel_determinant(labeled, 13, prime), hankel_determinant(orbits, 20, prime)
        assert all(residues)
        print(f'k={k}: independent order-13 and order-20 Hankel determinants mod {prime}: {residues}')


def read_terms(repo, aid):
    path = repo / 'seq' / aid[:4] / (aid + '.seq')
    terms = []
    for line in path.read_text().splitlines():
        if line[:2] in ('%S', '%T', '%U'):
            terms.extend(int(x) for x in line.split(maxsplit=2)[2].split(',') if x)
    return terms


def check_oeis(repo):
    for aid, formula in [('A233330', core), ('A233331', reduced_core),
                         ('A233332', corona), ('A233333', reduced_corona)]:
        expected = read_terms(repo, aid)
        pairs = ((n, k) for n in range(2, len(expected) + 2) for k in range(1, n // 2 + 1))
        differences = [(n, k, value, formula(n, k)) for value, (n, k) in zip(expected, pairs)
                       if formula(n, k) != value]
        reference_differences = [(4, 1, 414, 385)] if aid == 'A233333' else []
        assert differences == reference_differences, (aid, differences)
        print(f'{aid}: checked {len(expected)} source terms, differences {differences}')
    # The A233332 example block supplies three additional complete rows.
    source = (repo / 'seq/A233/A233332.seq').read_text().splitlines()
    rows = [line.split(maxsplit=2)[2] for line in source if line.startswith('%e A233332 .')]
    for n, row in enumerate(rows, start=2):
        expected = [int(x) for x in row.split('.') if x]
        assert expected == [corona(n, k) for k in range(1, n // 2 + 1)]
    print(f'A233332: all {len(rows)} full example rows agree')
    for t, value in enumerate(read_terms(repo, 'A233329')):
        assert reduced_core(t + 2, 1) == value
    terms = read_terms(repo, 'A235804')
    diagonals = (i + 1 + (t - i) * 2**i for t in range(len(terms)) for i in range(t, -1, -1))
    assert all(a == b for a, b in zip(terms, diagonals))
    print(f'A233329 and A235804: all {len(read_terms(repo, "A233329"))} and {len(terms)} entry terms agree')


def check():
    for n in range(2, 17):
        for k in range(1, n // 2 + 1):
            assert direct_counts(n, k) == (core(n, k), corona(n, k)), (n, k)
    for n in range(2, 7):
        for k in range(1, n // 2 + 1):
            assert direct_orbits(n, k) == (reduced_core(n, k), reduced_corona(n, k)), (n, k)
    for n in range(2, 53):
        for k in range(1, n // 2 + 1):
            assert burnside_sum(n, k) == reduced_corona(n, k), (n, k)
    for k in range(1, 21):
        values = [corona(n, k) for n in range(2 * k, 2 * k + 65)]
        for root, multiplicity in [(4, 5), (2, 6), (1, 2)]:
            for _ in range(multiplicity):
                values = [b - root * a for a, b in zip(values, values[1:])]
        assert not any(values)
        values = [reduced_corona(n, k) for n in range(2 * k + 1, 2 * k + 66)]
        for step, root, mult in [(1, 4, 5), (1, 2, 6), (1, -2, 3), (2, 2, 3)]:
            for _ in range(mult):
                values = [b - root * a for a, b in zip(values, values[step:])]
        assert not any(values)
    for n in range(3, 141):
        for k in range(1, n // 2 + 1):
            assert (corona(n, k) - (n - 2)) % 2**(n - 3) == 0
        assert ((corona(n, 1) - (n - 2)) % 2**(n - 2) != 0) == (n % 8 in (4, 6))
        M = n // 2
        if n % 2 == 0:
            assert reduced_core(n, 1) == M * (M + 1) * (2 * M * M - 1) // 2
    print('All direct counts through n=16, literal symmetry orbits through n=6,')
    print('Burnside sums through n=52, both recurrences in 20 columns and congruences through n=140 agree.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--oeis-repo', type=Path, help='checkout of oeis/oeisdata')
    args = parser.parse_args()
    check()
    check_least_orders()
    if args.oeis_repo:
        check_oeis(args.oeis_repo)
