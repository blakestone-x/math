"""Verify the ternary lift on integer matrices and three-symbol cutoffs on all factors."""

from fractions import Fraction
from itertools import product
from math import gcd


def determinant(matrix):
    n = len(matrix)
    if n == 0:
        return 1
    sign, previous = 1, 1
    for j in range(n - 1):
        pivot = next((i for i in range(j, n) if matrix[i][j]), None)
        if pivot is None:
            return 0
        if pivot != j:
            matrix[j], matrix[pivot] = matrix[pivot], matrix[j]
            sign = -sign
        row = matrix[j]
        for i in range(j + 1, n):
            target = matrix[i]
            for k in range(j + 1, n):
                target[k], remainder = divmod(row[j] * target[k] - target[j] * row[k],
                                               previous)
                assert remainder == 0
        previous = row[j]
    return sign * matrix[-1][-1]


def hankel(word, order):
    return determinant([list(word[i:i + order]) for i in range(order)])


def rook(n):
    if n == 0:
        return 0
    odd_part = n // (n & -n)
    return (odd_part % 4) // 2


def pagoda(n):
    return rook(n + 1) - rook(n - 1)


def lift(target, length):
    letters = [0, 0]
    for n in range(length - 2):
        letters.append((2 * letters[-1] - letters[-2] + pagoda(n + 2 - target)) % 3)
    return [1 + 3 * y for y in letters]


def check_lifts():
    total = 0
    for target in [0, 2, 5, 23]:
        word = lift(target, 85)
        for start, order in product(range(31), range(1, 23)):
            value = hankel(word[start:], order)
            scale = 3 ** (order - 1)
            assert value % scale == 0
            subsequence = [pagoda(start + 2 - target + i)
                           for i in range(max(0, 2 * order - 3))]
            assert (value // scale - hankel(subsequence, order - 1)) % 3 == 0
            if (start - target) % (order & -order) == 0:
                assert (value // scale) % 3
                total += 1
    word = lift(2, 6)
    assert word == [1, 1, 7, 4, 4, 4] and hankel(word[3:], 2) == 0
    print(f"exact lift congruences {4 * 31 * 22}")
    print(f"predicted exact valuations checked {total}")


SUB = {"1": "13", "2": "23", "3": "14", "4": "24"}
CODE = {"1": (0, 1), "2": (1, -1), "3": (0, -1), "4": (1, 0)}


def state_pairs():
    # Every state appears in the fourth iterate of state 1.
    states = "1"
    for _ in range(4):
        states = "".join(SUB[x] for x in states)
    assert set(states) == set(SUB)
    pairs = set(SUB.values())
    while True:
        expanded = pairs | {SUB[x][-1] + SUB[y][0] for x, y in pairs}
        if expanded == pairs:
            return pairs
        pairs = expanded


def factors(length):
    blocks = CODE.copy()
    while len(blocks["1"]) < length:
        blocks = {symbol: blocks[left] + blocks[right]
                  for symbol, (left, right) in SUB.items()}
    words = set()
    for left, right in state_pairs():
        block = blocks[left] + blocks[right]
        words.update(block[i:i + length] for i in range(len(blocks[left])))
    assert len(words) <= 32 * length
    return words


def check_cutoff(cutoff=16):
    bad, total = set(), 0
    for order in range(1, cutoff + 1):
        words = factors(2 * order - 1)
        total += len(words)
        for word in words:
            constant = hankel(word, order)
            linear = hankel([x + 1 for x in word], order) - constant
            assert constant % 3 or linear % 3
            if linear:
                bad.add(Fraction(-constant, linear))
    candidates = [2 + Fraction(u, v) for u, v in product(range(1, 12 * cutoff + 1),
                                                          repeat=2) if gcd(u, v) == 1]
    assert len(set(candidates)) == len(candidates) > 36 * cutoff ** 2
    choice = next(q for q in candidates if q not in bad)
    v, u = choice.denominator, choice.numerator - 2 * choice.denominator
    for order in range(1, cutoff + 1):
        for word in factors(2 * order - 1):
            assert hankel([u + 2 * v + v * x for x in word], order)
    print(f"all-shift Dakota cutoff {cutoff}, distinct factors over these orders {total}")
    print(f"forbidden rational translations {len(bad)}")
    print(f"verified integer letters {[u + v, u + 2 * v, u + 3 * v]}")


if __name__ == "__main__":
    check_lifts()
    check_cutoff()
