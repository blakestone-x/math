"""Exact coefficients for partial transversals of finite abelian group tables.

Run `python3 partitions.py 6` for the coefficient tables for k=1,...,6.
Only the standard library is required.
"""

from argparse import ArgumentParser
from array import array
from collections import Counter
from itertools import permutations
from math import factorial, prod


def partitions(size):
    """Represent each block by a bit mask and sort the blocks as integers."""
    families = [()]
    for label in range(size):
        bit = 1 << label
        enlarged = []
        for family in families:
            enlarged.append((*family, bit))
            for i, block in enumerate(family):
                enlarged.append(tuple(sorted((*family[:i], *family[i+1:], block | bit))))
        families = enlarged
    return families


def actions(size, families):
    index = {blocks: i for i, blocks in enumerate(families)}
    result = []
    for perm in permutations(range(size)):
        mask_images = [0] * (1 << size)
        for mask in range(1, 1 << size):
            bit = mask & -mask
            mask_images[mask] = mask_images[mask ^ bit] | (1 << perm[bit.bit_length() - 1])
        result.append(array('H', (index[tuple(sorted(mask_images[b] for b in blocks))]
                                  for blocks in families)))
    return result


def orbits(group, images):
    """Return a representative, its multiplicity, and the point stabilizer."""
    todo = set(range(len(images[0])))
    while todo:
        rep = min(todo)
        orbit = {images[g][rep] for g in group}
        todo.difference_update(orbit)
        stab = [g for g in group if images[g][rep] == rep]
        yield rep, len(orbit), stab


def diagonal_factors(matrix):
    """Unimodular Euclidean row/column operations. Divisibility order is unnecessary."""
    factors = []
    while matrix and matrix[0]:
        pivot = next(((i, j) for i, row in enumerate(matrix)
                      for j, value in enumerate(row) if value), None)
        if pivot is None:
            break
        i, j = pivot
        matrix[0], matrix[i] = matrix[i], matrix[0]
        for row in matrix:
            row[0], row[j] = row[j], row[0]
        while True:
            a = matrix[0][0]
            for i in range(1, len(matrix)):
                if matrix[i][0] % a:
                    quotient = matrix[i][0] // a
                    matrix[i] = [x - quotient*y for x, y in zip(matrix[i], matrix[0])]
                    matrix[0], matrix[i] = matrix[i], matrix[0]
                    break
            else:
                for j in range(1, len(matrix[0])):
                    if matrix[0][j] % a:
                        quotient = matrix[0][j] // a
                        for row in matrix:
                            row[j] -= quotient * row[0]
                            row[0], row[j] = row[j], row[0]
                        break
                else:
                    break
                continue
            continue
        # Clear the first column by row operations. Clearing the first row
        # then leaves the remaining lower-right block untouched.
        factors.append(abs(a))
        matrix = [[x - (row[0] // a)*y for x, y in zip(row[1:], matrix[0][1:])]
                  for row in matrix[1:]]
    return factors


def signature(blocks, size):
    # Rename the three coordinates so the last partition has the most blocks.
    # Coordinate symmetry follows from the equivalent equation x+y+z=0.
    first, second, last = sorted(blocks, key=len)
    count = len(first) + len(second)
    columns = [[0]*size for _ in range(2)]
    for column, block in enumerate((*first, *second)):
        for i in range(size):
            if block & (1 << i):
                columns[column >= len(first)][i] = column
    matrix = []
    for block in last:
        representative = (block & -block).bit_length() - 1
        for i in range(representative + 1, size):
            if block & (1 << i):
                row = [0]*count
                for coord in columns:
                    row[coord[i]] += 1
                    row[coord[representative]] -= 1
                matrix.append(row)
    factors = diagonal_factors(matrix)
    return count - len(factors), tuple(sorted(d for d in factors if d > 1))


def coefficients(size):
    families = partitions(size)
    weights = [prod((-1)**(b.bit_count()-1) * factorial(b.bit_count()-1) for b in family)
               for family in families]
    images = actions(size, families)
    totals = Counter()
    visited = 0
    for a, count_a, stab_a in orbits(range(len(images)), images):
        for b, count_b, stab_ab in orbits(stab_a, images):
            for c, count_c, _ in orbits(stab_ab, images):
                multiplicity = count_a * count_b * count_c
                key = signature((families[a], families[b], families[c]), size)
                totals[key] += multiplicity * weights[a] * weights[b] * weights[c]
                visited += multiplicity
    assert visited == len(families)**3
    return {key: value for key, value in sorted(totals.items()) if value}


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('max_k', type=int, nargs='?', default=6, choices=range(1,8))
    args = parser.parse_args()
    for k in range(1, args.max_k + 1):
        print(k, coefficients(k), flush=True)
