"""Verify and print small fixed-length codes in the unit-cost edit metric."""

import argparse
from collections import Counter
from itertools import combinations

SEED_8 = (
    "1333310", "3322223", "3100111", "1111022",
    "2231133", "0220000", "0002332", "2013201",
)
SEED_16 = (
    "0020", "0101", "0332", "0213", "1003", "1122", "1311", "1230",
    "2031", "2110", "2323", "2202", "3012", "3133", "3300", "3221",
)


def distance(left, right):
    previous = list(range(len(right) + 1))
    for i, a in enumerate(left, 1):
        current = [i]
        for j, b in enumerate(right, 1):
            current.append(min(previous[j] + 1, current[j-1] + 1,
                               previous[j-1] + (a != b)))
        previous = current
    return previous[-1]


def code(seed, repeats, trim=0):
    return tuple("".join(c * repeats for c in word)[trim:] for word in seed)


def verify(words, expected_distance):
    assert len(set(words)) == len(words)
    assert len({len(word) for word in words}) == 1
    pairs = Counter(distance(a, b) for a, b in combinations(words, 2))
    assert min(pairs) >= expected_distance
    print(f"{len(words)} words of length {len(words[0])}; pair distances {dict(sorted(pairs.items()))}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--words", action="store_true", help="print the certified codewords")
    args = parser.parse_args()
    for seed, repeats, trim, minimum in [
        (SEED_8, 1, 0, 6), (SEED_8, 2, 0, 12), (SEED_8, 2, 1, 11),
        (SEED_16, 1, 0, 3), (SEED_16, 3, 0, 9), (SEED_16, 4, 0, 12),
    ]:
        words = code(seed, repeats, trim)
        verify(words, minimum)
        if args.words:
            print("\n".join(words))


if __name__ == "__main__":
    main()
