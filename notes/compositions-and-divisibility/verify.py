#!/usr/bin/env python3
"""Exact checks accompanying Compositions and a divisibility theorem for OEIS A115047."""

from decimal import Decimal, localcontext
from fractions import Fraction
from itertools import groupby
from math import comb, factorial, gcd, prod


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def compositions(total):
    """All ordered lists of positive parts with the given total."""
    if total == 0:
        yield ()
        return
    for first in range(1, total + 1):
        for tail in compositions(total - first):
            yield (first,) + tail


def volumes_through(limit):
    values = [0] * (limit + 1)
    values[3] = 1
    for n in range(4, limit + 1):
        total = sum(
            comb(n - 4, i - 1) * comb(n, i + 1) * i * (n - i - 2)
            * values[i + 2] * values[n - i]
            for i in range(1, n - 2)
        )
        values[n], remainder = divmod(total, 2 * (n - 1))
        require(remainder == 0, f"Nonintegral recurrence at {n}")
    return values


def volume_by_multinomials(n):
    """Kaufmann-Manin-Zagier formula, Proposition 33 of Alexandersson-Jordan."""
    size = n - 3
    value = Fraction(0)
    for parts in compositions(size):
        k = len(parts)
        first = factorial(size) // prod(factorial(p) for p in parts)
        second = factorial(size + k) // prod(factorial(p + 1) for p in parts)
        value += Fraction((-1) ** (size - k) * first * second, factorial(k))
    return value


def check_volumes():
    prefix = [1, 1, 5, 61, 1379, 49946, 2648967, 193530835,
              18634276859, 2286742481794, 348390662991293,
              64519134394428000, 14273926322439378685]
    limit = 120
    values = volumes_through(limit)
    require(values[3:3 + len(prefix)] == prefix, "A115047 tabulated values")
    for n in range(4, 16):
        require(values[n] == volume_by_multinomials(n), f"Independent formula at {n}")
    for n in range(3, limit + 1):
        require(values[n] % (n // gcd(n, 12)) == 0, f"Divisibility at {n}")
        for j in range(2, n - 1):
            left = (n - 1) * (n - 2) * (n - 3) * comb(n - 4, j - 2) * comb(n, j)
            right = (n * (j - 1) * (n - j - 1)
                     * comb(n - 1, j - 1) * comb(n - 1, j))
            require(left == right, f"Binomial identity at {(n, j)}")
    for candidate in range(1, 12):
        require(any((candidate * values[n]) % n for n in (3, 4)),
                f"Sharpness at multiplier {candidate}")
    print("A115047: recurrence, binomial identity and divisibility through n=120.")
    print("         Independent multinomial formula at n=4..15; 1..11 excluded by n=3,4.")


def encode_blocks(blocks, ordinary_weight, step):
    """Encode (is_distinguished, count) blocks in the proof's common word alphabet."""
    word = []
    after_marker = False
    index = 0
    while index < len(blocks):
        special, count = blocks[index]
        if special and index + 1 == len(blocks):
            word.extend([step] * count)
        elif special:
            word.extend([step] * (count - 1))
            word.append(ordinary_weight + step)
            index += 1
            next_special, following_count = blocks[index]
            require(not next_special, "Two distinguished blocks")
            word.extend([step] * following_count)
            after_marker = True
        elif after_marker:
            word.append(ordinary_weight)
            word.extend([step] * count)
        else:
            word.extend([step] * count)
            word.append(ordinary_weight)
        index += 1
    return tuple(word)


def common_words(total, has_marker=False):
    if total == 0:
        yield ()
        return
    for letter in (1, 2, 3):
        if letter > total or (letter == 3 and has_marker):
            continue
        for tail in common_words(total - letter, has_marker or letter == 3):
            yield (letter,) + tail


def one_run_blocks(parts):
    blocks = []
    runs = 0
    for is_one, group in groupby(parts, key=lambda p: p == 1):
        if is_one:
            runs += 1
            blocks.append((True, sum(1 for _ in group)))
        else:
            blocks.extend((False, p - 2) for p in group)
    return blocks if runs <= 1 else None


def check_bijections():
    prefix = [1, 1, 2, 4, 7, 13, 23, 41, 72, 126, 219, 379,
              653, 1121, 1918, 3272, 5567]
    for n, expected in enumerate(prefix):
        targets = set(common_words(n))
        even_images = []
        run_images = []
        for parts in compositions(n):
            if sum(p % 2 == 0 for p in parts) <= 1:
                blocks = [(p % 2 == 0, p // 2) for p in parts]
                even_images.append(encode_blocks(blocks, 1, 2))
            blocks = one_run_blocks(parts)
            if blocks is not None:
                run_images.append(encode_blocks(blocks, 2, 1))
        for images in (even_images, run_images):
            require(len(images) == len(targets) == expected, f"Cardinality at {n}")
            require(set(images) == targets, f"Image of the map at {n}")
    print("A208354: both bijections hit each target exactly once for weights 0..16.")


def pair_count(total, min_part):
    """Counts ordered pairs via independent left and right single-composition totals."""
    singles = [0] * (total + 1)
    singles[0] = 1
    running = 0
    for s in range(min_part, total + 1):
        running += singles[s - min_part]
        singles[s] = running
    return sum(singles[i] * singles[total - i] for i in range(total + 1))


def range_count(n):
    return sum(
        pair_count(n - m, m) - pair_count(n - m, m + 1)
        for m in range(1, n // 2 + 1)
    )


def check_range_asymptotic():
    prefix = [0, 2, 3, 12, 23, 61, 135, 306, 679, 1499, 3257, 7053,
              15167, 32443, 69080, 146533, 309743, 652762, 1371897,
              2876284, 6017100, 12562511, 26180328, 54469099, 113151406,
              234723068, 486276265, 1006195365, 2079647131, 4293758081,
              8856361762, 18250277543]
    for n, expected in enumerate(prefix, start=1):
        require(range_count(n) == expected, f"A323111 tabulated value at {n}")
        if n <= 10:
            actual = sum(max(parts) - min(parts) == n for parts in compositions(2 * n))
            require(actual == expected, f"Independent enumeration at {n}")
    print("A323111: all compositions of 2n enumerated at n=1..10; OEIS terms 1..32 agree.")
    with localcontext() as context:
        context.prec = 50
        phi = (1 + Decimal(5).sqrt()) / 2
        limit = 1 / (5 * phi ** 5)
        print(f"         Predicted limit K = {limit:.12f}")
        for n in (100, 500, 1000):
            # Perform the near-cancellation in integers before taking a decimal ratio.
            difference = (n + 2) * 2 ** (n - 3) - range_count(n)
            ratio = Decimal(difference) / (n * phi ** n)
            print(f"         n={n:4}  ((n+2)2^(n-3)-a(n))/(n*phi^n) = {ratio:.12f}")


if __name__ == "__main__":
    check_volumes()
    check_bijections()
    check_range_asymptotic()
