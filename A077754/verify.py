"""Exhaust the finite range used in the proof of A077754."""


def has_witness(n):
    residues = [set() for _ in range(n + 1)]
    for first in range(1, 10):
        for second in range(1, 10):
            if first + second <= n:
                residues[first + second].add((10 * first + second) % n)

    for digit_sum in range(2, n):
        for digit in range(1, min(9, n - digit_sum) + 1):
            residues[digit_sum + digit].update(
                (10 * residue + digit) % n for residue in residues[digit_sum]
            )
    return 0 in residues[n]


if __name__ == "__main__":
    absent = [n for n in range(1, 100) if not has_witness(n)]
    expected = [n for n in range(1, 100) if n % 10 == 0 or n in (1, 2, 5, 11)]
    if absent != expected:
        raise AssertionError((absent, expected))
    print("Verified 1 through 99. Missing indices:", *absent)
