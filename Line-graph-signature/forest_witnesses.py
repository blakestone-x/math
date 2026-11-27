"""Reconstruct attaining root graphs and compute exact line-adjacency inertias."""
from sympy import zeros


def variations(coefficients):
    signs = [1 if a > 0 else -1 for a in coefficients if a]
    return sum(a != b for a, b in zip(signs, signs[1:]))


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
    adjacency = zeros(len(edges))
    for i, edge in enumerate(edges):
        for j in range(i):
            if set(edge).intersection(edges[j]):
                adjacency[i, j] = adjacency[j, i] = 1
    polynomial = adjacency.charpoly().all_coeffs()
    positive = variations(polynomial)
    negative = variations([a * (-1)**i for i, a in enumerate(polynomial)])
    nullity = len(edges) - positive - negative
    assert positive - negative == (cycles + 1) // 2
    print(f'{cycles} cycles, {vertices} root vertices, line inertia (+,0,-) '
          f'= ({positive},{nullity},{negative}), signature {positive-negative}.')


if __name__ == '__main__':
    for count in range(10, 14):
        chain(count)
