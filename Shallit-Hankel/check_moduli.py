"""Independent exact determinant checks of the six witnesses and small-modulus searches."""
from functools import lru_cache
from pathlib import Path

from verify_gcd import determinant


@lru_cache(maxsize=180000)
def hankel(window):
    r = (len(window)+1)//2
    return determinant([list(window[j:j+r]) for j in range(r)])


def exact_extrema(m):
    deepest = 0
    count = 0
    def extend(word):
        nonlocal deepest, count
        deepest = max(deepest, len(word))
        count += 1
        for x in range(1, m):
            candidate = word + (x,)
            if all(hankel(candidate[-d:]) % m for d in range(3, len(candidate)+1, 2)):
                extend(candidate)
    extend(())
    return deepest, count


if __name__ == "__main__":
    records = Path(__file__).with_name("moduli-verification.txt").read_text().splitlines()
    expected = (2, 4, 24, 22, 42, 52)
    for j, length in enumerate(expected):
        m = j+2
        witness = tuple(map(int, records[2*j+1].split()[1]))
        assert len(witness) == length
        checked = 0
        for n in range(1, length+1, 2):
            for s in range(length-n+1):
                assert hankel(witness[s:s+n]) % m
                checked += 1
        print(f"m={m}: {checked} nonzero minors in a length-{length} witness")
        if m <= 5:
            maximum, nodes = exact_extrema(m)
            assert maximum == length
            print(f"m={m}: independent unnormalized search, {nodes} nodes including the empty word")
