"""Enumerate rotation classes directly, including every prescribed color content."""

from collections import Counter
from itertools import product
from math import factorial, prod


def split_length(n):
    power = n & -n
    return power, n // power


def all_colors(q, n):
    _, h = split_length(n)
    return (q**((n + 1) // 2) + q**((h + 1) // 2)) // 2


def labeled_palindromes(content):
    if sum(value % 2 for value in content) != sum(content) % 2:
        return 0
    return factorial(sum(content) // 2) // prod(factorial(v // 2) for v in content)


def by_content(content):
    power, _ = split_length(sum(content))
    odd_period = 0
    if all(v % power == 0 for v in content):
        odd_period = labeled_palindromes(tuple(v // power for v in content))
    return (labeled_palindromes(content) + odd_period) // 2


def enumerate_necklaces(q, n):
    observed = Counter()
    contents = set()
    for word in product(range(q), repeat=n):
        content = tuple(word.count(color) for color in range(q))
        contents.add(content)
        rotations = [word[i:] + word[:i] for i in range(n)]
        if word == min(rotations) and any(v == v[::-1] for v in rotations):
            observed[content] += 1
    assert all(observed[c] == by_content(c) for c in contents)
    assert sum(observed.values()) == all_colors(q, n)


if __name__ == "__main__":
    for q, max_length in ((1, 12), (2, 14), (3, 9), (4, 7)):
        for n in range(1, max_length + 1):
            enumerate_necklaces(q, n)
    listed = [2, 3, 6, 9, 20, 34, 72, 129, 272, 516, 1056, 2050, 4160,
              8200, 16512, 32769, 65792, 131088, 262656, 524292, 1049600,
              2097184, 4196352, 8388610, 16781312, 33554496, 67117056,
              134217736, 268451840, 536871040, 1073774592, 2147483649]
    assert listed == [all_colors(2, 2*n) for n in range(1, len(listed) + 1)]
    print("Verified all tested necklaces, their individual color counts, and 32 OEIS terms.")
