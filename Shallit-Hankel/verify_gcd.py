"""Check the finite extension tables and small independent determinant examples."""
from itertools import product
from math import gcd

SUBSTITUTION = {"1": "12", "2": "23", "3": "14", "4": "32"}
PAIRS = {"12", "14", "21", "22", "23", "31", "32", "41", "42"}
DIRECT = {0: 4, 1: 8, 2: 13, 3: 18, 4: 20, 5: 36, 6: 36, 7: 40}
SCALED = {4: 20, 5: 30, 6: 32, 7: 40, 8: 40}


def inflate(word, rounds):
    for _ in range(rounds):
        word = "".join(SUBSTITUTION[letter] for letter in word)
    return word


def factors(length):
    block = 1
    rounds = 0
    while block < length:
        block *= 2
        rounds += 1
    out = set()
    for pair in PAIRS:
        word = inflate(pair, rounds)
        out.update(word[i:i + length] for i in range(block))
    return out


def splits(word, history, scaled):
    seen = {}
    for i in range(history, len(word)):
        prefix = word[i-history:i]
        symbol = int(word[i])
        earlier = seen.setdefault(prefix, set())
        if scaled:
            if any((other == 2) != (symbol == 2) for other in earlier):
                return True
        elif any(abs(other - symbol) == 1 for other in earlier):
            return True
        earlier.add(symbol)
    return False


def check_tables():
    start = inflate("1", 5)
    assert set(start[i:i+2] for i in range(len(start)-1)) == PAIRS
    assert set(SUBSTITUTION.values()) <= PAIRS
    assert {SUBSTITUTION[a][-1] + SUBSTITUTION[b][0] for a, b in PAIRS} <= PAIRS
    for name, table in (("direct", DIRECT), ("scaled", SCALED)):
        for h, duration in table.items():
            words = factors(h + duration)
            assert all(splits(w, h, name == "scaled") for w in words)
            shorter = factors(h + duration - 1)
            assert any(not splits(w, h, name == "scaled") for w in shorter)
            print(f"{name:6} h={h} D={duration:2} factors={len(words)}")


def determinant(a):
    """Exact division-free on singular pivots, fraction-free otherwise."""
    n = len(a)
    previous = 1
    sign = 1
    for j in range(n-1):
        pivot = next((i for i in range(j, n) if a[i][j]), None)
        if pivot is None:
            return 0
        if pivot != j:
            a[pivot], a[j] = a[j], a[pivot]
            sign *= -1
        for i in range(j+1, n):
            for k in range(j+1, n):
                numerator = a[i][k]*a[j][j] - a[i][j]*a[j][k]
                assert numerator % previous == 0
                a[i][k] = numerator // previous
        previous = a[j][j]
    return sign * a[-1][-1]


if __name__ == "__main__":
    check_tables()
    word = list(map(int, inflate("1", 9)))
    def hankel(s, r):
        return determinant([word[s+i:s+i+r] for i in range(r)])
    for s, r in product(range(12), range(1, 8)):
        assert gcd(*(hankel(s+i, r) for i in range((13*r+1)//2))) == 1
        assert gcd(*(hankel(s, k) for k in range(r, (15*r)//2+1))) == 1
    print("84 horizontal and 84 vertical gcds checked by integer elimination.")
