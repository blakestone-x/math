"""Check exact ring periods, infinite-line templates, and OEIS generating functions."""

from math import gcd


# Positive-width exceptional prefixes. The elementary formula applies thereafter.
PREFIX = {
    9: [2, 2, 2, 2, 2, 9, 5, 12, 18, 5],
    25: [2, 2, 3, 2, 15, 15, 21, 16, 9],
    41: [2, 2, 2, 2, 15, 2],
    107: [2, 2, 3, 2, 15, 2, 28, 2, 36, 20, 11, 12, 117, 28, 60, 8],
    190: [1, 1, 1],
}
SHIFT = {9: (4, 2, 2), 25: (4, 2, 1), 41: (0, 4, 4), 107: (7, 4, 4)}
TEMPLATES = {
    9: [(0, "1"), (-1, "111"), (0, "101"), (-1, "11111"), (0, "11101"),
        (-1, "1011111"), (2, "11101")],
    25: [(0, "1"), (-1, "11"), (-1, "101"), (-2, "1111"), (-2, "11101"),
         (-3, "101111"), (-1, "11101")],
    41: [(0, "1"), (-1, "111"), (0, "101"), (-1, "11011"), (4, "1")],
    107: [(0, "1"), (0, "11"), (-1, "1011"), (-1, "10001"), (-2, "1110111"),
          (-1, "1000101"), (-2, "111011011"), (-1, "100000001"), (-2, "11100000111"),
          (-1, "10100000101"), (-2, "1101100011011"), (3, "100000001")],
}

# Coefficients of the numerator after dividing it by x, as printed by Colin Barker.
NUMERATOR = {
    9: [2, 2, -2, -2, 0, 7, 3, -4, 10, -10, -9, 14, 0, -5],
    25: [2, -2, 1, -2, 14, -13, 6, -11, -2, 18, -9],
    41: [2, 2, 2, 2, 11, -2, 24, 4, 8, 18, -10, -2, -5, -10],
    107: [2, 2, 3, 2, 11, -2, 22, -2, 8, 18, -42, 10, 60, -10, 66, -14,
          -130, 0, -33, 16, 65, 0, 0, -8],
    190: [1, 1, 1, 4, 3, 4, 5, -4, 0, -1, -2],
}


def period_formula(rule, n):
    if n < 1:
        return 0  # zero extension for generating-function coefficients
    if n <= len(PREFIX[rule]):
        return PREFIX[rule][n - 1]
    if rule == 190:
        return 4 if n % 4 == 0 else n
    _, duration, shift = SHIFT[rule]
    return duration * n // gcd(shift, n)


def ring_step(state, n, rule):
    """Evaluate Wolfram's truth table in parallel on n bits with cyclic wrap."""
    mask = (1 << n) - 1
    left = ((state << 1) & mask) | (state >> (n - 1))
    right = (state >> 1) | ((state & 1) << (n - 1))
    new = 0
    for code in range(8):
        if (rule >> code) & 1:
            matches = left if code & 4 else ~left
            matches &= state if code & 2 else ~state
            matches &= right if code & 1 else ~right
            new |= matches
    return new & mask


def orbit_period(rule, n):
    first = {}
    state = 1
    while state not in first:
        first[state] = len(first)
        state = ring_step(state, n, rule)
    return len(first) - first[state]


def check_templates(rule):
    defects = {0}
    for t, (start, pattern) in enumerate(TEMPLATES[rule]):
        assert defects == {start + j for j, bit in enumerate(pattern) if bit == "1"}
        background = t % 2
        next_background = (rule >> (7 * background)) & 1
        assert next_background == 1 - background
        new = set()
        for i in range(min(defects) - 1, max(defects) + 2):
            bits = [background ^ (k in defects) for k in (i - 1, i, i + 1)]
            if ((rule >> (4 * bits[0] + 2 * bits[1] + bits[2])) & 1) != next_background:
                new.add(i)
        defects = new


def check_190_wedge():
    ones = {0}
    for t in range(61):
        assert ones == {-t + j for j in range(2*t + 1) if j % 4 != 3}
        new = set()
        for i in range(-t - 1, t + 2):
            code = 4*((i - 1) in ones) + 2*(i in ones) + ((i + 1) in ones)
            if (190 >> code) & 1:
                new.add(i)
        ones = new


def main():
    for rule in SHIFT:
        check_templates(rule)
    check_190_wedge()
    for rule in PREFIX:
        lag = {9: 2, 25: 1}.get(rule, 4)
        expected = NUMERATOR[rule]
        for n in range(1, 161):
            a = period_formula(rule, n)
            assert orbit_period(rule, n) == a, (rule, n)
            residual = a - 2*period_formula(rule, n - lag) + period_formula(rule, n - 2*lag)
            assert residual == (expected[n - 1] if n <= len(expected) else 0), (rule, n)
    print("All templates, 800 directly measured ring periods, and five rational numerators agree.")
    print("Rule 190 recurrence residuals at widths 10 and 11 are -1 and -2.")


if __name__ == "__main__":
    main()
