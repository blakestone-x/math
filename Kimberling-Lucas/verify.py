"""Independent checks using literal greedy subtraction and Morrison's Wythoff array."""
from bisect import bisect_right
from collections import Counter
from math import isqrt


def recurrence(first, second, count):
    values = [first, second]
    while len(values) < count:
        values.append(values[-1] + values[-2])
    return values


F = recurrence(0, 1, 121)
L = recurrence(2, 1, 121)


def weights(basis, bound):
    coins = sorted({v for v in basis if 0 < v <= bound})
    counts = bytearray(bound + 1)
    for x in range(1, bound + 1):
        leading = coins[bisect_right(coins, x) - 1]
        counts[x] = 1 + counts[x - leading]
    return counts


def check_weights(bound):
    z, u, w = (weights(b, bound) for b in (F, L, F + L))
    expected = {1, 2, 3, 5, 6, 8, 9, 10, 16, 17}
    for h in range(7, len(L)):
        offsets = (1, 2, 3, 5) if h % 2 else (1, 2)
        expected.update(L[h] - d for d in offsets if L[h] - d <= bound)
    zeros = set()
    first = {}
    difference = 0
    for x in range(1, bound + 1):
        first.setdefault(w[x], x)
        difference += z[x] - u[x]
        assert difference >= 0
        if difference == 0:
            zeros.add(x)
    assert zeros == expected
    assert list(first.values()) == [(F[3*t+1] - 1)//2 for t in range(1,len(first)+1)]

    polys = [Counter((z[x], w[x]) for x in range(f)) for f in F if f <= bound+1]
    for i in range(4, len(polys)):
        together = polys[i-1].copy()
        for shift, parts in ((1, polys[i-3]), (2, polys[i-4])):
            for (a,b), frequency in parts.items():
                together[a+shift,b+1] += frequency
        assert together == polys[i]
    print(f"All {bound} inclusive prefixes checked; {len(zeros)} equality indices match the classification.")
    print(f"All {len(first)} observed first occurrences and {len(polys)-4} bivariate block recurrences checked.")


def floor_phi(n):
    return (n + isqrt(5*n*n)) // 2


def check_rows(rows, columns):
    sequences = []
    for n in range(1,rows+1):
        a = floor_phi(n)
        x = [a*L[k] + (n-1)*L[k-1] for k in range(1,columns+2)]
        sequences.append((n, a, x))
    bound = max(x[-2] for _,_,x in sequences)
    # Morrison's two original floor formulas and the Fibonacci row recurrence.
    successor = {}
    n = 1
    while True:
        a = floor_phi(n)
        x = floor_phi(a)
        if x > bound:
            break
        y = floor_phi(a) + a
        while x <= bound:
            assert x not in successor
            successor[x] = y
            x, y = y, x+y
        n += 1
    assert len(successor) == bound
    for n, a, row in sequences:
        early = floor_phi(5*n-2) >= 5*a-1
        inserted = floor_phi(5*n-1) < 5*a+2
        permanent = 3 if early else 5
        first = 1 if n == 1 else 2 if inserted else 4
        for entries, tail, literal in ((row, permanent, permanent),
                                        ([row[0],row[0]+1]+row[1:], permanent+1, first)):
            adjacent = [successor[x] == y for x,y in zip(entries[:columns],entries[1:])]
            assert adjacent.index(True)+1 == literal
            assert next(j for j in range(1,columns+1) if all(adjacent[j-1:])) == tail
    print(f"Both row-entry formulas checked in {rows} rows through column {columns}, using {bound} Wythoff successors.")


if __name__ == "__main__":
    check_weights(350000)
    check_rows(2000, 10)
