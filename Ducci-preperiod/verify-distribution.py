"""Verify modular Ducci preperiod distributions by graph enumeration and matrix reduction."""

from itertools import product
from math import prod


def prime_powers(modulus):
    p = 2
    while p * p <= modulus:
        exponent = 0
        while modulus % p == 0:
            exponent += 1
            modulus //= p
        if exponent:
            yield p, exponent
        p += 1
    if modulus > 1:
        yield modulus, 1


def valuation(n, p):
    result = 0
    while n % p == 0:
        n //= p
        result += 1
    return result


def local_kernel_exponent(p, k, exponent, steps):
    rank = min(k, exponent)
    return (exponent - rank) * min(steps, 1) + sum(
        min(steps, p ** (k - j) * (1 + (p - 1) * (exponent - j + 1)))
        for j in range(1, rank + 1)
    )


def cumulative_count(modulus, width, steps):
    if width % 2:
        e = valuation(modulus, 2)
        return modulus**width // (2 ** max(e - steps, 0))
    counts = []
    for p, exponent in prime_powers(modulus):
        k = valuation(width, p)
        invertible_dimension = width - p**k
        kernel_exponent = local_kernel_exponent(p, k, exponent, steps)
        counts.append(p ** (exponent * invertible_dimension + kernel_exponent))
    return prod(counts)


def enum_distribution(modulus, width):
    """Find cyclic vertices by taking images, then compute successive full preimages."""
    transitions = {}
    for state in product(range(modulus), repeat=width):
        shifts = state[1:] + state[:1]
        transitions[state] = tuple((a + b) % modulus for a, b in zip(state, shifts))
    current = set(transitions)
    while True:
        image = {transitions[state] for state in current}
        if len(image) == len(current):
            break
        current = image
    counts = [len(current)]
    while len(current) != len(transitions):
        current = {state for state, target in transitions.items() if target in current}
        counts.append(len(current))
    return counts


def log_kernel_from_matrix(matrix, p, exponent):
    """Count modular solutions by extracting unit pivots; divide the remaining block by p."""
    if not matrix or exponent == 0:
        return 0
    modulus = p**exponent
    work = [row[:] for row in matrix]
    size = len(work)
    rank = 0
    while rank < size:
        pivot = next(
            ((i, j) for i in range(rank, size) for j in range(rank, size) if work[i][j] % p),
            None,
        )
        if pivot is None:
            break
        i, j = pivot
        work[i], work[rank] = work[rank], work[i]
        for row in work:
            row[j], row[rank] = row[rank], row[j]
        pivot_row = work[rank]
        inverse = pow(pivot_row[rank], -1, modulus)
        for i in range(rank + 1, size):
            scale = work[i][rank] * inverse % modulus
            if scale:
                work[i] = [(a - scale * b) % modulus for a, b in zip(work[i], pivot_row)]
        rank += 1
    reduced = [[value // p for value in row[rank:]] for row in work[rank:]]
    # Each free variable modulo p^(exponent-1) has p lifts. The pivot variables
    # are then uniquely forced by the top rows.
    return size - rank + log_kernel_from_matrix(reduced, p, exponent - 1)


def check_cyclic_matrices(p, k, exponent):
    size = p**k
    modulus = p**exponent
    column = [1] + [0] * (size - 1)
    powers = 0
    while True:
        # The columns of (I-shift)^powers are cyclic shifts of this column.
        columns = [column[i:] + column[:i] for i in range(size)]
        found = log_kernel_from_matrix(columns, p, exponent)
        expected = local_kernel_exponent(p, k, exponent, powers)
        assert found == expected, (p, k, exponent, powers, found, expected)
        if not any(column):
            return powers + 1
        column = [(a - b) % modulus for a, b in zip(column, column[-1:] + column[:-1])]
        powers += 1


def main():
    spaces = states = 0
    for modulus in range(2, 14):
        for width in range(1, 11):
            if modulus**width > 50000:
                continue
            counts = enum_distribution(modulus, width)
            expected = [cumulative_count(modulus, width, h) for h in range(len(counts))]
            assert counts == expected, (modulus, width, counts, expected)
            spaces += 1
            states += modulus**width
    print(f"Complete graphs: {spaces} modulus-width pairs, {states} configurations.")

    parameters = [(2, k) for k in range(6)] + [(3, k) for k in range(4)]
    parameters += [(5, k) for k in range(3)] + [(7, k) for k in range(3)] + [(11, 1)]
    powers = triples = 0
    for p, k in parameters:
        for exponent in range(1, 8):
            powers += check_cyclic_matrices(p, k, exponent)
            triples += 1
    print(f"Cyclic matrices: {triples} parameter triples, {powers} powers.")


if __name__ == "__main__":
    main()
