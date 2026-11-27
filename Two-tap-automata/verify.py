"""Check width-dividing periods by direct time evolution, with no root computations."""

from itertools import product
from math import gcd, lcm


def field_tables(size):
    if size == 4:
        # Binary coefficients in 1,w with w^2 = w+1.
        def multiply(i, j):
            value = (i if j & 1 else 0) ^ ((i << 1) if j & 2 else 0)
            return value ^ (7 if value & 4 else 0)

        return 2, [[i ^ j for j in range(4)] for i in range(4)], [
            [multiply(i, j) for j in range(4)] for i in range(4)
        ]
    return size, [[(i + j) % size for j in range(size)] for i in range(size)], [
        [(i * j) % size for j in range(size)] for i in range(size)
    ]


def scalar_order(value, mul):
    if value == 0:
        raise ValueError("Zero has no multiplicative order")
    current = value
    length = 1
    while current != 1:
        current = mul[current][value]
        length += 1
    return length


def predict(p, n, u, v, alpha, beta, add, mul):
    m = n
    while m % p == 0:
        m //= p
    thickness = n // m
    thickness //= gcd(thickness, gcd(u, v))
    if m <= 2:
        residues = [add[alpha][beta]]
        if m == 2:
            neg = [row.index(0) for row in add]
            residues.append(add[neg[alpha] if u % 2 else alpha][neg[beta] if v % 2 else beta])
        orders = [scalar_order(h, mul) for h in residues if h]
        period = lcm(*orders) * thickness if orders else 1
        return period if n % period == 0 else None

    q = m + 1
    size_check = q
    while size_check % p == 0:
        size_check //= p
    if size_check != 1 or any(m % scalar_order(h, mul) for h in (alpha, beta)):
        return None
    field_factor = m
    if q == 4 and u * pow(v - u, -1, m) % m == 1 and mul[alpha][alpha] == beta:
        field_factor = 1
    return field_factor * thickness


def measured(n, u, v, alpha, beta, add, mul):
    weighted_sum = [
        [add[mul[alpha][left]][mul[beta][right]] for right in range(len(mul))]
        for left in range(len(mul))
    ]
    shift_u = [(i - u) % n for i in range(n)]
    shift_v = [(i - v) % n for i in range(n)]

    def step(state):
        return [weighted_sum[state[i]][state[j]] for i, j in zip(shift_u, shift_v)]

    state = [1] + [0] * (n - 1)
    for _ in range(n):
        state = step(state)
    # The images of an endomorphism of an n-dimensional space stabilize by n.
    cycle_start = state
    for length in range(1, n + 1):
        state = step(state)
        if state == cycle_start:
            return length if n % length == 0 else None
    return None


def main():
    for size in (2, 3, 4, 5, 7):
        p, add, mul = field_tables(size)
        number = 0
        qualifying = 0
        for n in range(1, 33):
            m = n
            while m % p == 0:
                m //= p
            for u, gap in product((-6, -2, -1, 0, 1, 2, 3, 4), (1, 2, 3, 4, 5, 6)):
                if gcd(gap, m) != 1:
                    continue
                v = u + gap
                for alpha, beta in product(range(1, size), repeat=2):
                    expected = predict(p, n, u, v, alpha, beta, add, mul)
                    found = measured(n, u, v, alpha, beta, add, mul)
                    assert found == expected, (size, n, u, v, alpha, beta, found, expected)
                    number += 1
                    qualifying += found is not None
        print(f"GF({size}): {number} comparisons, {qualifying} periods divide the width")
    _, add, mul = field_tables(2)
    assert measured(21, 1, 4, 1, 1, add, mul) == 21
    print("Connected width-21 counterexample verified.")


if __name__ == "__main__":
    main()
