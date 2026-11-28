"""Exact decimal audit for the two classes in the rotation manuscript."""
from math import prod
from gaps import PRIMES, radical_within, rough_part, smooth_numbers

PRIMES_7 = PRIMES[7]
LARGEST_C = 8_251_953_408
EXPECTED = (
    12, 18, 21, 24, 27, 36, 42, 45, 48, 54, 63, 72, 81, 84, 108, 243,
    324, 405, 432, 450, 486, 504, 540, 567, 648, 675, 756, 810, 864,
    1008, 4050, 5040, 8100,
)


def audit(height=LARGEST_C):
    denominator_bound = 10 * 90009 * height
    width = 1
    while 10**width - 1 <= 63 * width * denominator_bound:
        width += 1
    max_width = width - 1
    assert max_width == 18 and 9 * 4375 < 10**5
    uncovered = {(a, b) for a in range(1, 10) for b in range(1, 10)
                 if not radical_within(rough_part(10000*a+b, PRIMES_7), 10_000_000 // prod(PRIMES_7))}
    assert uncovered == {(5,3),(5,9),(6,1),(6,7),(7,1),(7,3),(7,9),(8,9),(9,1),(9,7)}
    numbers = smooth_numbers(PRIMES_7, 10**max_width - 1)
    members = set(numbers)
    found = []
    two_digits = []
    for n in numbers:
        word = str(n)
        positions = [i for i, digit in enumerate(word) if digit != "0"]
        if len(positions) < 2:
            continue
        if not all(int(word[i:] + word[:i]) in members for i in range(len(word))):
            continue
        spacings = [b - a for a, b in zip(positions, positions[1:] + [positions[0] + len(word)])]
        assert min(spacings) <= 3
        found.append(n)
        if len(positions) == 2:
            two_digits.append(n)
    assert tuple(found) == EXPECTED
    print(f"rotation audit: width <= {max_width}, {len(numbers)} smooth integers, "
          f"{len(found)} nontrivial values, {len(two_digits)} with exactly two nonzero digits")
    return found


if __name__ == "__main__":
    audit()
