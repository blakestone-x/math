"""Check the three ternary variation recurrences by ranking words independently.

No external dependencies. Rank 1 means the first (smallest) member of a row.
The checks support the all-rank proof in Proof.md.
"""
from functools import cache


def change(mode, left, right):
    if mode == 'total':
        return abs(right - left)
    if mode == 'down':
        return max(0, left - right)
    return max(0, right - left)


def ranked_rows(mode, max_row, ranks):
    @cache
    def completions(left, remaining, target):
        if not 0 <= target <= 2 * remaining:
            return 0
        if remaining == 0:
            return int(target == 0)
        return min(ranks, sum(completions(digit, remaining - 1,
                              target - change(mode, left, digit)) for digit in range(3)))

    def unrank(target, rank):
        length = 1
        while True:
            for lead in (1, 2):
                count = completions(lead, length - 1, target)
                if rank > count:
                    rank -= count
                    continue
                value = digit = lead
                for remaining in range(length - 2, -1, -1):
                    for nxt in range(3):
                        residual = target - change(mode, digit, nxt)
                        count = completions(nxt, remaining, residual)
                        if rank > count:
                            rank -= count
                            continue
                        value = 3 * value + nxt
                        target, digit = residual, nxt
                        break
                    else:
                        raise AssertionError('suffix rank exceeds available completions')
                assert target == 0
                return value
            length += 1

    return [[unrank(n, k) for k in range(1, ranks + 1)] for n in range(max_row + 1)]


def verify(mode, rows, ranks):
    observed = [[] for _ in rows]
    for x in range(1, 20001):
        digits = []
        v = x
        while v:
            v, d = divmod(v, 3)
            digits.append(d)
        n = sum(change(mode, hi, lo) for lo, hi in zip(digits, digits[1:]))
        if len(observed[n]) < ranks:
            observed[n].append(x)
    for expected, ranked in zip(observed, rows):
        assert expected == ranked[:len(expected)]
    for j in range(ranks):
        col = [row[j] for row in rows]
        for n in range(4 * (j + 1) + 12, len(col) - 4):
            if mode == 'total':
                assert col[n + 4] == 2*col[n + 2] + 3*col[n] + 2
            else:
                assert col[n + 2] == 9*col[n] + (6 if mode == 'down' else 2)
    col = [row[0] for row in rows]
    if mode == 'total':
        assert col[:6] == [1, 3, 6, 11, 20, 33]
        for n in range(6, len(col)):
            assert col[n] == col[n-1] + 2*col[n-2] - 2*col[n-3] + 3*col[n-4] - 3*col[n-5]
    elif mode == 'down':
        assert col[:4] == [1, 3, 6, 33]
        assert all(col[n+2] == 9*col[n] + 6 for n in range(1, len(col)-2))
    else:
        assert col[:3] == [1, 5, 11]
        assert all(col[n+2] == 9*col[n] + 2 for n in range(len(col)-2))


if __name__ == '__main__':
    count, last_row = 32, 160
    for mode in ('total', 'down', 'up'):
        verify(mode, ranked_rows(mode, last_row, count), count)
        print(f'{mode}: checked {count} columns through row {last_row} and direct ranks below 20001')
