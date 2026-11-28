"""Independent exact checks on the integral forms, modular fibers and OEIS formula."""
from collections import Counter
from itertools import product
from math import gcd, prod
from sympy import Matrix, ZZ
from sympy.matrices.normalforms import smith_normal_form


def axis_matrix(n, left, right, periodic):
    matrix = [[0]*n for _ in range(n)]
    for i in range(n):
        for j in range(i-left, i+right+1):
            if periodic or 0 <= j < n:
                matrix[i][j % n] += 1
    return matrix


def axis_factors(n, left, right, periodic):
    length = left+right+1
    if periodic:
        g = gcd(n, length)
        return [1]*(n-g) + [length//g] + [0]*(g-1)
    exterior_left = {j % length for j in range(1-left,1)}
    exterior_right = {j % length for j in range(n+1,n+right+1)}
    d = len(exterior_left & exterior_right)
    return [1]*(n-d) + [0]*d


def literal_image(sizes, axes, modulus):
    coords = list(product(*(range(n) for n in sizes)))
    index = {coord: i for i, coord in enumerate(coords)}
    displacements = list(product(*(range(-a,b+1) for a,b,_ in axes)))
    windows = []
    for cell in coords:
        sites = []
        for delta in displacements:
            pos = tuple(i+j for i,j in zip(cell,delta))
            if all(cyclic or 0 <= j < n for j,n,(_,_,cyclic) in zip(pos,sizes,axes)):
                sites.append(index[tuple(j%n for j,n in zip(pos,sizes))])
        windows.append(sites)
    counts = Counter()
    for array in product(range(modulus), repeat=len(coords)):
        output = tuple(sum(array[i] for i in sites) % modulus for sites in windows)
        counts[output] += 1
    return counts


def empirical(n,k):
    s,v = n%3, k%3
    coeff = 3*n - 3*(s*s-s)//2
    return ((3*((n-1)//3)+s*s-3*s+3) + ((k-1)//3)*coeff
            + (v*v-3*v+2)*(coeff//3))


if __name__ == "__main__":
    for n,left,right,cyclic in product(range(1,12), range(5), range(5), (False,True)):
        literal = Matrix(axis_matrix(n,left,right,cyclic))
        smith = smith_normal_form(literal, domain=ZZ)
        assert [abs(int(smith[i,i])) for i in range(n)] == axis_factors(n,left,right,cyclic)
        if not cyclic and left == right:
            r = left
            s = n % (2*r+1)
            assert axis_factors(n,r,r,False).count(0) == max(0,min(s-1,2*r+1-s))
    print("550 one-axis integer Smith forms agree, including short and wrapped axes.")

    test_boxes = [
        ((2,2), ((1,1,False),(1,1,True)),6),
        ((2,3), ((0,2,False),(2,1,True)),3),
        ((2,2,2), ((2,0,True),(0,1,False),(1,1,True)),2),
        ((3,3), ((1,1,False),(1,1,False)),2),
    ]
    for sizes, axes, modulus in test_boxes:
        diag = [prod(v) for v in product(*(axis_factors(n,*axis) for n,axis in zip(sizes,axes)))]
        kernel = prod(gcd(modulus,t) for t in diag)
        counts = literal_image(sizes, axes, modulus)
        assert set(counts.values()) == {kernel}
        assert len(counts)*kernel == modulus**prod(sizes)
    for n,k in product(range(1,101), repeat=2):
        assert empirical(n,k) == (n-int(n%3==2))*(k-int(k%3==2))
    print("Exhaustive image and fiber checks passed for four mixed boxes.")
    print("The printed OEIS expression agrees on all 10,000 tested size pairs.")
