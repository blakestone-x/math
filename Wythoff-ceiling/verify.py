"""Cross-check the defining ceiling array, greedy Fibonacci digits, and block recurrences."""

from bisect import bisect_right
from collections import Counter
from functools import cache
from math import isqrt

LIMIT = 250_000
GAPS = (3, 5, 10, 13)
EXPONENT = {0: 4, 3: 6, 5: 7, 10: 8, 13: 7}
STATES = [None] + [(r, v) for r in range(3) for v in (None, False, True)]
FIB = [0, 1]
while len(FIB) <= 65:
    FIB.append(sum(FIB[-2:]))


def array_counts(limit):
    counts = bytearray(limit + 1)
    n = 1
    while True:
        ceiling = (n + isqrt(5 * n * n)) // 2 + 1
        a = ceiling + n - 1
        if a > limit:
            return counts
        b = 2 * ceiling + n - 1
        while a <= limit:
            counts[a] += 1
            a, b = b, a + b
        n += 1


def fibonacci_multiplicity(n):
    """Greedy decomposition uses F_2=1 as the least available summand."""
    indices = []
    while n:
        i = bisect_right(FIB, n) - 1
        indices.append(i)
        n -= FIB[i]
    r = indices[-1] - 2
    if len(indices) == 1:
        return r % 2
    v = indices[-2] - indices[-1] - 2
    return r % 2 + v % 2 + int(r == 0 and v % 2 == 0)


def zero(state):
    if state is None:
        return None
    r, v = state
    return (2 if r == 1 else 1, v)


def one(state):
    if state is None:
        return (0, None)
    return (0, state[0] != 1)


def mark(kind, state):
    if state is None:
        return False
    r, v = state
    if kind == "doubled":
        return r == 1 and v is True
    return r == 2 and v is not True


def join(left, right):
    a, first, last, counts = left
    b, head, tail, counts2 = right
    counts = counts + counts2
    if last is not None and head is not None:
        counts[last + 1 + head] += 1
    if first is None and head is not None:
        first = a + head
    if tail is None and last is not None:
        tail = b + last
    return a + b, first, tail, counts


@cache
def block(kind, k, state):
    if k == 0:
        if mark(kind, state):
            return 1, 0, 0, Counter({0: 1})
        return 1, None, None, Counter()
    if k == 1:
        return join(block(kind, 0, zero(state)), block(kind, 0, one(state)))
    return join(block(kind, k - 1, zero(state)), block(kind, k - 2, zero(one(state))))


def shape(data):
    length, first, last, counts = data
    if first is None:
        return (length,)
    return first, last, set(counts).issubset({0, *GAPS})


def residual(kind, g, k, state):
    return block(kind, k, state)[3][g] - FIB[k + 2 - EXPONENT[g]]


def main():
    counts = array_counts(LIMIT)
    assert all(counts[n] == fibonacci_multiplicity(n) for n in range(1, LIMIT + 1))
    sets = {
        "doubled": [n for n in range(1, LIMIT + 1) if counts[n] == 2],
        "omitted tail": [n for n in range(2, LIMIT + 1) if counts[n] == 0],
    }
    assert counts[1] == 0 and sets["omitted tail"][0] == 3
    print(f"Exact array versus greedy Fibonacci digits: all {LIMIT:,} positive inputs agree.")
    for kind, members in sets.items():
        gaps = Counter(y - x for x, y in zip(members, members[1:]))
        assert set(gaps) == set(GAPS)
        print(f"{kind}: {len(members):,} members through {LIMIT:,}; internal gaps {sorted(gaps.items())}.")
        for state in STATES:
            for k in (8, 9):
                assert shape(block(kind, k + 2, state)) == shape(block(kind, k, state))
                for g in EXPONENT:
                    a, b, c = (residual(kind, g, k + j, state) for j in (0, 2, 4))
                    assert a + c == 2 * b and abs(b - a) <= 1 and abs(a) <= 6
        for k in range(2, 61):
            data = block(kind, k, None)
            assert data[0] == FIB[k + 2] and set(data[3]).issubset({0, *GAPS})
            if k >= 4:
                m = k // 2
                if kind == "doubled":
                    expected = FIB[k - 2] - (1 if k % 2 else m - 1)
                else:
                    expected = FIB[k - 2] + (m - 1 if k % 2 else 0)
                assert data[3][0] == expected
            if FIB[k + 2] - 1 <= LIMIT:
                prefix = members[:bisect_right(members, FIB[k + 2] - 1)]
                actual = Counter(y - x for x, y in zip(prefix, prefix[1:]))
                actual[0] = len(prefix)
                assert data[3] == +actual
        print(f"{kind}: boundary and affine-count certificates pass for every state and statistic.")
    print("The unique exceptional gap in the direct enumeration is 1 to 3.")


if __name__ == "__main__":
    main()
