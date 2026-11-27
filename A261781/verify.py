"""Exact checks for the column generating functions of OEIS A261781."""

from itertools import product
from math import comb


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def multiply(a, b):
    result = [0] * (len(a) + len(b) - 1)
    for i, left in enumerate(a):
        for j, right in enumerate(b):
            result[i + j] += left * right
    return result


def unrestricted_column(j, limit):
    values = [1] + [0] * limit
    if j:
        for n in range(1, limit + 1):
            values[n] = sum(comb(j + s - 1, s) * values[n - s] for s in range(1, n + 1))
    return values


def count_words_with_cuts(n, k):
    """A descent must be cut; each of the other positions may be cut or uncut."""
    count = 0
    for word in product(range(k), repeat=n):
        if len(set(word)) == k:
            optional_cuts = sum(a <= b for a, b in zip(word, word[1:]))
            count += 2 ** optional_cuts
    return count


def polynomial_gcd_degree(a, b, prime):
    def trim(poly):
        while poly and poly[-1] == 0:
            poly.pop()
        return poly

    a = trim([c % prime for c in a])
    b = trim([c % prime for c in b])
    while b:
        inverse = pow(b[-1], -1, prime)
        while len(a) >= len(b):
            offset = len(a) - len(b)
            factor = a[-1] * inverse % prime
            for i, c in enumerate(b):
                a[offset + i] = (a[offset + i] - factor * c) % prime
            trim(a)
        a, b = b, a
    return len(a) - 1


def verify():
    limit = 100
    unrestricted = [unrestricted_column(j, limit) for j in range(9)]
    den = [1]
    for k in range(1, 9):
        factor = [1] + [2 * (-1) ** s * comb(k, s) for s in range(1, k + 1)]
        den = multiply(den, factor)
        degree = k * (k + 1) // 2
        require(len(den) - 1 == degree, f"Degree at {k}")
        column = [
            sum((-1) ** (k - j) * comb(k, j) * unrestricted[j][n] for j in range(k + 1))
            for n in range(limit + 1)
        ]
        numerator = multiply(den, column)[:limit + 1]
        require(all(c == 0 for c in numerator[degree + 1:]), f"Recurrence at {k}")
        require(polynomial_gcd_degree(den, numerator[:degree + 1], 1000003) == 0,
                f"Common factor modulo 1000003 at {k}")
        if k <= 4:
            for n in range(1, 8):
                require(column[n] == count_words_with_cuts(n, k), f"Word enumeration at {(n,k)}")
        if k == 3:
            require(column[3:10] == [13, 132, 924, 5546, 30720, 162396, 834004],
                    "Published ternary column")
    print("Exact recurrences through n=100, and coprime numerators/denominators for k=1..8.")
    print("Independent marked-word enumeration through n=7 for k=1..4.")


if __name__ == "__main__":
    verify()
