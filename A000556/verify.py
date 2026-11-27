"""Exact checks for the four least-period formulas in periods.pdf (Python 3)."""

from math import comb, lcm


NAMES = ("A000556", "A000557", "A354242", "A354253")


def factors(n):
    p = 2
    while p * p <= n:
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        if e:
            yield p, e
        p += 1
    if n > 1:
        yield n, 1


def carmichael_power(p, e):
    if p == 2 and e >= 3:
        return 2**(e - 2)
    return (p - 1) * p**(e - 1)


def predicted_period(name, p, e):
    if p == 2:
        if name == "A000557" and e >= 4:
            return 2**(e - 3)
        if name == "A354242":
            return 1 if e <= 3 else max(2, 2**max(0, e - 5))
        if name == "A354253":
            return 1 if e <= 6 else max(2, 2**max(0, e - 7))
    if p == 3:
        if name in ("A000557", "A354242") and e == 1:
            return 1
        if name == "A354253" and e <= 5:
            return 3**(e - 1)
    return carmichael_power(p, e)


def weights(name, stop):
    if name in ("A000556", "A000557"):
        a, b = (1, 1) if name == "A000556" else (1, 2)
        for _ in range(stop):
            yield a
            a, b = b, a + b
    else:
        d = 1 if name == "A354242" else 2
        for i in range(stop):
            yield comb(2*i, i) * d**i


def power_coefficients(name, stop, modulus):
    """Coefficients of sum_{j < stop} g_j (X-1)^j in the monomial basis."""
    coefficients = [0] * stop
    for j, weight in enumerate(weights(name, stop)):
        for u in range(j + 1):
            coefficients[u] += (-1)**(j-u) * comb(j, u) * weight
    return [a % modulus for a in coefficients]


def first_factorial_multiple(m):
    j, value = 0, 1
    while value % m:
        j += 1
        value *= j
    return j


def block_period(values):
    size = len(values)
    for d in range(1, size + 1):
        if size % d == 0 and values[d:] == values[:-d]:
            return d
    raise AssertionError("A finite block must repeat after its full length")


def prime_power_block(name, p, e):
    modulus = p**e
    coefficients = power_coefficients(name, first_factorial_multiple(modulus), modulus)
    length = carmichael_power(p, e)
    return [sum(a * pow(u, n, modulus) for u, a in enumerate(coefficients)) % modulus
            for n in range(e, e + length)]


def egf_values(limit):
    """A separate exact calculation from the four defining differential identities."""
    result = {k: [1] for k in NAMES}
    for n in range(1, limit + 1):
        row = [comb(n, j) for j in range(n + 1)]
        kernel = [row[j] * (2**j - 1) for j in range(1, n + 1)]
        for name, numerator in (("A000556", 0), ("A000557", 1)):
            values = result[name]
            values.append(numerator + sum(k * a for k, a in zip(kernel, reversed(values))))
        for name, d in (("A354242", 4), ("A354253", 8)):
            values = result[name]
            row_before = [row[j] * (n - j) // n for j in range(n)]
            first = sum(row_before[j] * values[j] for j in range(n))
            second = sum(row_before[j] * values[j + 1] for j in range(n - 1))
            values.append((d // 2) * first + d * second)
    return result


def check_finite_cases():
    cases = [(2, e) for e in range(1, 14)]
    cases += [(3, e) for e in range(1, 7)] + [(5, 1), (5, 2)]
    for name in NAMES:
        for p, e in cases:
            assert block_period(prime_power_block(name, p, e)) == predicted_period(name, p, e)
    assert prime_power_block("A000556", 2, 5) == [15, 25, 23, 1, 31, 9, 7, 17]
    assert prime_power_block("A000557", 2, 5) == [2, 0, 18, 0, 2, 0, 18, 0]
    print("Complete periodic blocks checked at every finite base case for all four sequences.")


def check_prime_calculation():
    for p in range(7, 200):
        if list(factors(p)) != [(p, 1)]:
            continue
        split = pow(5, (p - 1) // 2, p) == 1
        for name in NAMES:
            coeff = power_coefficients(name, 2*p, p)
            u1 = (coeff[1] + coeff[p + 1]) % p
            if name == "A000556":
                target = 1 if split else -5
            elif name == "A000557":
                target = 1 if split else 3
            else:
                target = (2 if name == "A354242" else 4) * u1
            assert coeff[p + 1] == target % p != 0, (p, name)
    print("Checked the symbolic first-lift coefficient for every prime from 7 through 199.")


def check_separate_recurrences(limit=500):
    values = egf_values(limit + limit.bit_length())
    assert values["A000556"][:6] == [1, 1, 5, 31, 257, 2671]
    assert values["A000557"][:6] == [1, 2, 8, 50, 416, 4322]
    assert values["A354242"][:6] == [1, 2, 14, 158, 2486, 50222]
    assert values["A354253"][:6] == [1, 4, 52, 1108, 32980, 1261204]
    exceptions = []
    for m in range(1, limit + 1):
        powers = list(factors(m))
        length = lcm(*(carmichael_power(p, e) for p, e in powers))
        start = max((e for _, e in powers), default=0)
        for name in NAMES:
            block = [a % m for a in values[name][start:start + length]]
            expected = lcm(*(predicted_period(name, p, e) for p, e in powers))
            assert block_period(block) == expected, (name, m)
            if name == "A000557" and expected != length and m <= 200:
                exceptions.append(m)
    assert exceptions == [3, 6, 16, 32, 48, 64, 96, 112, 128, 144, 160, 176, 192]
    print(f"Independent generating-function recurrences verified all four formulas for m=1..{limit}.")
    print("A000557 exceptions through 200:", exceptions)


if __name__ == "__main__":
    check_finite_cases()
    check_prime_calculation()
    check_separate_recurrences()
