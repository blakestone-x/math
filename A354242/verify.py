"""Exact coefficient checks by two independent expansions and modular examples."""

from fractions import Fraction
from math import comb, factorial, gcd, lcm


def stirling_rows(n):
    row = [1]
    yield row
    for i in range(1, n + 1):
        row = [0] + [row[j - 1] + j * row[j] for j in range(1, i)] + [1]
        yield row


def moment_coefficients(c, r, n):
    weights = [1]
    for j in range(n):
        weights.append(weights[-1] * c * (r + j))
    return [sum(s * w for s, w in zip(row, weights)) for row in stirling_rows(n)]


def sfraction_coefficients(c, r, n):
    # Each additional level can first affect one later coefficient.
    tail = [1] + [0] * n
    for level in range(n, 0, -1):
        j = (level + 1) // 2
        alpha = c * (j + r - 1) if level % 2 else (1 + c) * j
        reciprocal = [1]
        for k in range(1, n + 1):
            reciprocal.append(alpha * sum(tail[i] * reciprocal[k - 1 - i] for i in range(k)))
        tail = reciprocal
    return tail


def modulus_parameters(m):
    exponent = 1
    for u in range(1, m):
        if gcd(u, m) == 1:
            order = next(j for j in range(1, m) if pow(u, j, m) == 1)
            exponent = lcm(exponent, order)
    largest, remainder = 0, m
    for p in range(2, m + 1):
        e = 0
        while remainder % p == 0:
            e += 1
            remainder //= p
        largest = max(largest, e)
    return largest, exponent


def check_example(seq, m, onset, block):
    """The theorem makes a whole universal block sufficient to certify the example."""
    start, shift = modulus_parameters(m)
    assert shift % len(block) == 0
    for n in range(onset, max(onset, start) + shift):
        assert seq[n] % m == block[(n - onset) % len(block)]
    assert all(block != block[j:] + block[:j] for j in range(1, len(block)))
    assert seq[onset - 1] % m != block[-1]


def main():
    half = Fraction(1, 2)
    for c, r, degree in ((4, half, 32), (8, half, 32), (3, 2, 25),
                         (Fraction(1, 3), Fraction(5, 7), 18)):
        assert moment_coefficients(c, r, degree) == sfraction_coefficients(c, r, degree)
    first, second = [moment_coefficients(c, half, 32) for c in (4, 8)]
    assert first[:10] == [1, 2, 14, 158, 2486, 50222, 1239254, 36126638, 1214933846,
                          46299580142]
    assert second[:10] == [1, 4, 52, 1108, 32980, 1261204, 58928212, 3253363348,
                           207225008980, 14958174725524]
    check_example(first, 16, 3, [14, 6])
    check_example(second, 7, 1, [4, 3, 2, 3, 0, 0])
    rows = list(stirling_rows(100))
    for coefficients in ([(-2)**j for j in range(101)], [comb(2*j, j) for j in range(101)],
                         [j*j - 3*j + 1 for j in range(101)]):
        weights = [factorial(j) * g for j, g in enumerate(coefficients)]
        values = [sum(a * b for a, b in zip(row, weights)) for row in rows]
        for m in range(2, 51):
            start, shift = modulus_parameters(m)
            assert all((values[n + shift] - values[n]) % m == 0
                       for n in range(start, len(values) - shift))
    print("Both continued fractions matched through degree 32, as did two further parameter tests.")
    print("Verified the two exact modular examples and tested three series at moduli 2 through 50.")


if __name__ == "__main__":
    main()
