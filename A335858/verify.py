"""Independently sort by run lengths and compare with the two OEIS maps."""

from itertools import groupby


def digits(x):
    return format(x, "b")


def runs(x):
    return tuple(sum(1 for _ in group) for _, group in groupby(digits(x)))


def reflect(x):
    word = digits(x)[::-1]
    if len(runs(x)) % 2 == 0:
        word = word.translate(str.maketrans("01", "10"))
    return int(word, 2)


def check(max_length):
    f = [0, 1]
    for n in range(2, 1 << max_length):
        m = f[n // 2]
        f.append(2 * m + 1 - (n % 2 + m % 2) % 2)
    for length in range(1, max_length + 1):
        indices = range(1 << (length - 1), 1 << length)
        left = sorted(indices, key=runs)
        right = sorted(indices, key=lambda x: runs(x)[::-1])
        if left != [f[n] for n in indices]:
            raise AssertionError(("left", length))
        if right != [reflect(f[n]) for n in indices]:
            raise AssertionError(("right", length))
    print(f"Both orders verified for all positive indices below 2^{max_length}.")


if __name__ == "__main__":
    check(15)
