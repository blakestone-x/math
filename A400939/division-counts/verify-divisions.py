"""Literal walk checks for Division counts in the generalized halving Recaman walk."""
from math import gcd, isqrt


def triangle(n):
    return n * (n + 1) // 2


def first_source(k):
    for n in range(1, 2 * k + 1):
        q, remainder = divmod(triangle(n), k)
        if remainder == 0 and isqrt(8 * q + 1) ** 2 != 8 * q + 1:
            return n
    raise AssertionError(k)


def ceil_sqrt(number):
    return 1 + isqrt(number - 1)


def arithmetic_prediction(k):
    n = first_source(k)
    offset = triangle(n + 1) - triangle(n) // k
    odd = k // (k & -k)
    discriminant = 8 * offset + 1
    has_second = any((x * x - discriminant) % odd == 0 for x in range(odd))
    return n + 1, has_second


def prime_powers(limit):
    for p in range(2, limit + 1):
        if any(p % d == 0 for d in range(2, isqrt(p) + 1)):
            continue
        k, exponent = p, 1
        while k <= limit:
            yield k, p, exponent
            k *= p
            exponent += 1


def literal_walk(k, end, stop_after_two=False, check_collisions=False):
    a = 1
    seen = {1: (1, 0)}
    divisions = []
    blocked = 0
    for n in range(1, end):
        quotient, remainder = divmod(a, k)
        if remainder == 0 and quotient not in seen:
            a = quotient
            divisions.append(n + 1)
            if stop_after_two and len(divisions) == 2:
                break
        else:
            if check_collisions and remainder == 0:
                j, old_offset = seen[quotient]
                offset = triangle(n) - a
                b = 1 - k + 8 * (offset - k * old_offset)
                x, y = 2 * n + 1, 2 * j + 1
                assert x * x - k * y * y == b and b % 2
                common = gcd(x, y)
                modulus = abs(b) // (common * common)
                if modulus > 1:
                    root = (x // common) * pow(y // common, -1, modulus) % modulus
                    assert (root * root - k) % modulus == 0
                blocked += 1
            a += n + 1
        seen.setdefault(a, (n + 1, triangle(n + 1) - a))
    return divisions, blocked


def main():
    limit = 512
    prime_power_cases = {k: (p, e) for k, p, e in prime_powers(limit)}
    count_one = count_two = 0
    for k in range(2, limit + 1):
        d, two = arithmetic_prediction(k)
        deadline = ceil_sqrt(16 * k ** 3) + 6 * k
        observed, _ = literal_walk(k, deadline, stop_after_two=True)
        assert observed[0] == d and (len(observed) == 2) == two, k
        if k in prime_power_cases:
            p, e = prime_power_cases[k]
            one = (p != 2 and p % 5 in {2, 3}) or (p == 5 and e >= 2)
            assert one == (not two), k
        count_one += not two
        count_two += two
    print(f"k=2..{limit}: {count_one} single, {count_two} second divisions, "
          f"{len(prime_power_cases)} prime powers.")
    for k in [2, 4, 8, 16, 32]:
        divisions, blocked = literal_walk(k, 100_000, check_collisions=True)
        print(f"k={k}: {len(divisions)} divisions, {blocked} blocked through index 100000.")


if __name__ == "__main__":
    main()
