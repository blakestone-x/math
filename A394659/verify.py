"""Reproduce the finite certificate for the polynomial in OEIS A394659."""
import numpy as np


# Q in P(n) = (n - 4) Q(n) / 645120, in descending degree.
COEFFICIENTS = (
    1, 25, 9, -3555, -7745, 260563, 291075, -11898033,
    10339924, 303368632, -909281184, -2609966352,
    16737321600, -23213352960,
)


def proposed_count(n):
    polynomial = 0
    for coefficient in COEFFICIENTS:
        polynomial = polynomial * n + coefficient
    value, remainder = divmod((n - 4) * polynomial, 645120)
    if remainder:
        raise ArithmeticError(f"Nonintegral candidate at n={n}")
    return value


def verify():
    # Rows of the array index masks. Columns index cardinalities 0 through 7.
    # Up to side 20 the grid has at most 231 vertices. Even the unrestricted
    # count of size-j subsets is at most binom(231, 7) < 2**63 for j <= 7.
    previous = np.zeros((1, 8), dtype=np.int64)
    previous[0, 0] = 1
    for width in range(1, 22):
        # Subset sums: previous[allowed] will sum all masks inside allowed.
        for bit in range(width - 1):
            step = 1 << bit
            blocks = previous.reshape(-1, 2 * step, 8)
            blocks[:, step:] += blocks[:, :step]

        full_previous = (1 << (width - 1)) - 1
        current = np.zeros((1 << width, 8), dtype=np.int64)
        for mask in range(1 << width):
            occupied = mask.bit_count()
            if occupied > 7 or mask & (mask << 1):
                continue
            allowed = full_previous & ~(mask | (mask >> 1))
            current[mask, occupied:] = previous[allowed, :8 - occupied]

        previous = current
        n = width - 1
        if n >= 4:
            actual = int(current[:, 7].sum())
            expected = proposed_count(n)
            if actual != expected:
                raise ArithmeticError(f"n={n}: counted {actual}, expected {expected}")
            print(n, actual)


if __name__ == "__main__":
    verify()
