"""Reconstruct attaining root graphs and compute exact line-adjacency inertias."""
from sympy import zeros


def variations(coefficients):
    signs = [1 if a > 0 else -1 for a in coefficients if a]
    return sum(a != b for a, b in zip(signs, signs[1:]))


def line_inertia(edges):
    adjacency = zeros(len(edges))
    for i, edge in enumerate(edges):
        for j in range(i):
            if set(edge).intersection(edges[j]):
                adjacency[i, j] = adjacency[j, i] = 1
    polynomial = adjacency.charpoly().all_coeffs()
    positive = variations(polynomial)
    negative = variations([a * (-1)**i for i, a in enumerate(polynomial)])
    nullity = len(edges) - positive - negative
    return positive, nullity, negative


def chain(cycles):
    edges = []
    vertices = 0
    previous_attachment = None
    for index in range(cycles):
        size = 5 - index % 2
        edges.extend((vertices + i, vertices + (i + 1) % size) for i in range(size))
        if previous_attachment is not None:
            edges.append((previous_attachment, vertices))
        previous_attachment = vertices + 1
        vertices += size
    assert len(edges) - vertices + 1 == cycles
    positive, nullity, negative = line_inertia(edges)
    assert positive - negative == (cycles + 1) // 2
    print(f'{cycles} cycles, {vertices} root vertices, line inertia (+,0,-) '
          f'= ({positive},{nullity},{negative}), signature {positive-negative}.')


def square_gluing():
    hosts = [
        (1, []),
        (2, [(0, 1)]),
        (3, [(0, 1), (1, 2), (2, 0)]),
        (4, [(0, 1), (1, 2), (2, 3), (3, 0)]),
        (4, [(0, 1), (1, 2), (2, 0), (2, 3), (3, 0)]),
        (5, [(0, 1), (1, 2), (2, 0), (2, 3), (3, 4)]),
    ]
    cases = 0
    for n, first in hosts:
        first_inertia = line_inertia(first)
        square = [(n, n+1), (n+1, n+2), (n+2, n+3), (n+3, n)]
        for m, second in hosts:
            second_inertia = line_inertia(second)
            expected = tuple(a+b+d for a, b, d in zip(first_inertia, second_inertia, (3, 0, 3)))
            offset = n+4
            combined = first + square + [(a+offset, b+offset) for a, b in second]
            for u in range(n):
                for v in range(m):
                    joined = combined + [(u, n), (n+1, offset+v)]
                    assert line_inertia(joined) == expected
                    cases += 1
    print(f'Neutral-square gluing inertias agree in {cases} rooted pairs.')


if __name__ == '__main__':
    for count in range(10, 14):
        chain(count)
    square_gluing()
