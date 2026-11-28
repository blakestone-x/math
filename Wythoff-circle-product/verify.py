"""Exact integer checks against the original definitions of both products."""
from collections import Counter
from math import gcd, isqrt


def floor_phi(n):
    assert n >= 0
    return (n + isqrt(5*n*n)) // 2


def array_positions(limit):
    """Generate all ordinary row entries <= limit from the defining recurrence."""
    positions = {}
    r = 0
    while True:
        a = floor_phi(r+1)
        current, following = a+r, 2*a+r
        if current > limit:
            break
        col = 0
        while current <= limit:
            assert current not in positions
            positions[current] = (r, col)
            current, following = following, current + following
            col += 1
        r += 1
    assert len(positions) == limit
    return positions


def fib_digits(n, fib):
    digits = []
    for i in range(len(fib)-1, 1, -1):
        if fib[i] <= n:
            n -= fib[i]
            digits.append(i)
    assert n == 0
    return digits


def product_location(r, i, s, j):
    a, b = floor_phi(r+1), floor_phi(s+1)
    J, K = a*b+r*s, a*s+r*b-r*s
    pivot = floor_phi(K+1)
    if J < pivot:
        return 2*K-J, i+j+4
    if J > pivot:
        return J+K, i+j
    return K, i+j+2


def test_projection(bound):
    fib = [0, 1]
    while fib[-1] <= bound:
        fib.append(fib[-1] + fib[-2])
    max_index = len(fib)-1
    while len(fib) <= 2*max_index:
        fib.append(fib[-1]+fib[-2])
    digits = [[]]+[fib_digits(n, fib) for n in range(1, bound+1)]
    products = {(x, y): sum(fib[i+j] for i in digits[x] for j in digits[y])
                for x in range(1, bound+1) for y in range(1, bound+1)}
    positions = array_positions(max(products.values()))
    observed = Counter()
    for (x, y), z in products.items():
        r, i = positions[x]
        s, j = positions[y]
        assert positions[z] == product_location(r, i, s, j)
        observed[positions[z][1]-i-j] += 1
    assert set(observed) == {0, 2, 4}
    for x, y, z, location in ((6, 6, 84, (4, 4)), (4, 6, 58, (8, 2)), (4, 4, 40, (15, 0))):
        assert products[x, y] == z and positions[z] == location
    print(f'{bound**2} ordered digit products; every row and column matched the independent array.')
    print(f'Column offsets: {dict(sorted(observed.items()))}; array partition checked through {len(positions)}.')


def determinant(x, y):
    return y*y-x*y-x*x


def test_horadam(bound):
    for x in range(1, bound+1):
        for y in range(1, bound+1):
            h, k = x*x+2*x*y+2*y*y, (x+y)*(x+3*y)
            assert (2*y*(x+y))**2+(x*(x+2*y))**2 == h*h
            d = gcd(x, y)
            v = abs(determinant(x, y)) // d**2
            g = gcd(h, k)
            assert g == d*d*gcd(5, v)
            assert abs(determinant(h//g, k//g)) == (v//gcd(5, v))**2
    assert floor_phi(46) == 74 and determinant(119, 193) == 121
    assert gcd(134593, 217776) == 1 and determinant(134593, 217776) == -14641
    print(f'{bound**2} positive input pairs checked for the hypotenuse construction, including imprimitive pairs.')
    print('Row 45: (119,193), determinant 121; (134593,217776), gcd 1, absolute determinant 14641.')


if __name__ == '__main__':
    test_projection(256)
    test_horadam(300)
