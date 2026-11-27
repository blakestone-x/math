"""Check period equality directly from single-seed Rule 150 dynamics."""


def advance(state, n, steps):
    mask = (1 << n) - 1
    displacement = 1
    while steps:
        if steps & 1:
            d = displacement % n
            left = ((state << d) | (state >> (n - d))) & mask
            right = ((state >> d) | (state << (n - d))) & mask
            state ^= left ^ right
        displacement *= 2
        steps //= 2
    return state


def prime_factors(n):
    p = 2
    while p * p <= n:
        if n % p == 0:
            yield p
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        yield n


def period_equals_width(n):
    # The images of a linear map in dimension n stabilize by time n.
    state = advance(1, n, n)
    if advance(state, n, n) != state:
        return False
    return all(advance(state, n, n // p) != state for p in prime_factors(n))


def direct_period(n):
    state, seen = 1, {}
    while state not in seen:
        seen[state] = len(seen)
        state = advance(state, n, 1)
    return len(seen) - seen[state]


if __name__ == "__main__":
    for n in range(3, 34):
        if (direct_period(n) == n) != period_equals_width(n):
            raise AssertionError(("orbit", n))
    for n in range(3, 16_385):
        m = n // (n & -n)
        expected = m >= 7 and m & (m + 1) == 0
        if period_equals_width(n) != expected:
            raise AssertionError(("classification", n))
    print("Exact period-equality test passed for all widths 3 through 16384.")
