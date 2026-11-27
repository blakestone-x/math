"""Enumerate Lyndon words directly and compare their Euler products with the theorem."""

from itertools import product
from math import comb


def lyndon_columns(q, limit):
    counts = [[0] * (limit + 1) for _ in range(limit + 1)]
    for n in range(1, limit + 1):
        for word in product(range(q + 1), repeat=n):
            if not all(word < word[i:] + word[:i] for i in range(1, n)):
                continue
            k = next((i for i, letter in enumerate(word) if letter), n)
            counts[k][n] += 1
    return counts


def euler_product(column):
    limit = len(column) - 1
    result = [1] + [0] * limit
    for weight, count in enumerate(column):
        if count == 0:
            continue
        previous = result.copy()
        for times in range(1, limit // weight + 1):
            offset = times * weight
            ways = comb(count + times - 1, times)
            for n in range(offset, limit + 1):
                result[n] += ways * previous[n - offset]
    return result


def predicted(q, k, limit):
    blocks = [1] + [0] * limit
    for n in range(1, limit + 1):
        blocks[n] = q * sum(blocks[max(0, n - k - 1):n])
    result = [1] + [0] * limit
    for n in range(k + 1, limit + 1):
        result[n] = q * blocks[n - k - 1]
    if k == 1:
        for n in range(1, limit + 1):
            result[n] += result[n - 1]
    return result


def verify():
    for q, limit in ((1, 15), (2, 10), (3, 8)):
        columns = lyndon_columns(q, limit)
        for k in range(1, limit + 1):
            if euler_product(columns[k]) != predicted(q, k, limit):
                raise AssertionError(f"Euler product at q={q}, k={k}")
        if q == 1 and [columns[k][6] for k in range(7)] != [0, 2, 3, 2, 1, 1, 0]:
            raise AssertionError("Published binary row at length 6")
        print(f"Alphabet size {q + 1}: all columns agree through length {limit}.")


if __name__ == "__main__":
    verify()
