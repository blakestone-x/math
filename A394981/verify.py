"""Reproduce the sequence and check small boards by direct bar placement."""
import argparse
from collections import Counter
from functools import cache


def terms(max_height):
    """Count fixed-board tilings by number of available horizontal cuts."""
    if max_height < 1:
        return []
    counts = [1, 1]
    even = {2: 2}
    for height in range(2, max_height + 1):
        odd = {cuts + 1: cuts * count for cuts, count in even.items()}
        total = sum(odd.values())
        assert total % 4 == 0
        counts.extend((total // 4, total))
        even = Counter({cuts: 2 * count for cuts, count in odd.items()})
        even[2] += 2 * total
    return counts


def direct_count(n):
    """Place each length exactly once in either orientation on the grid."""
    height = (n + 1) // 2
    width = (n * (n + 1) // 2) // height
    masks = {}
    for length in range(1, n + 1):
        horizontal = (1 << length) - 1
        vertical = sum(1 << (i * width) for i in range(length))
        placements = [horizontal << (row * width + col)
                      for row in range(height)
                      for col in range(width - length + 1)]
        if length > 1:
            placements.extend(vertical << (row * width + col)
                              for row in range(height - length + 1)
                              for col in range(width))
        masks[length] = placements

    @cache
    def extend(length, used):
        if length == 0:
            return 1
        return sum(extend(length - 1, used | shape)
                   for shape in masks[length] if used & shape == 0)
    return extend(n, 0)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--through", type=int, default=10, choices=range(1, 13),
                        help="last index for direct placement (default 10)")
    direct_through = parser.parse_args().through
    published = [1, 1, 1, 4, 10, 40, 112, 448, 1360, 5440, 17728, 70912,
                 247936, 991744, 3736576, 14946304, 61103104, 244412416,
                 1092186112, 4368744448]
    values = terms(12)
    assert values[:len(published)] == published
    for n in range(1, direct_through + 1):
        fixed = direct_count(n)
        factor = 1 if n == 1 else 2 if n == 2 else 4
        assert fixed == factor * values[n - 1]
        print(f"n={n}: {fixed} fixed-board tilings")
    print("All 20 listed terms agree.")
    print("a(21) through a(24):", *values[20:24])
