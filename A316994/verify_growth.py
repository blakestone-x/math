"""Exact computation and independent finite checks for OEIS A316994."""

import argparse
import hashlib


def shifted_candidates(total, length):
    """Candidates of exactly 'length' bits with at least one trailing bit."""
    low = 1 << (length - 1)
    high = min(total, 2 * low - 1)
    for shift in range(1, (2 * total).bit_length() - length + 1):
        divisor = (1 << shift) - 1
        residue = total % (1 << (length + shift))
        candidate, remainder = divmod(residue, divisor)
        if low <= candidate <= high:
            yield candidate
        if remainder == 0 and low <= candidate - 1 <= high:
            yield candidate - 1


def next_term(total, used, first_unused):
    # All positive x below the largest 2-power dividing total are legal suffixes.
    if first_unused < (total & -total):
        return first_unused
    for length in range(first_unused.bit_length(), total.bit_length() + 1):
        options = [
            x for x in shifted_candidates(total, length)
            if x >= first_unused and x not in used
        ]
        if options:
            return min(options)
    raise AssertionError("The current sum is always a legal unused prefix.")


def direct_next(total, used, first_unused):
    for x in range(first_unused, total + 1):
        if x not in used and format(x, "b") in format(total + x, "b"):
            return x
    raise AssertionError("The direct search found no legal term.")


def check_offsets(maximum):
    pairs = 0
    for total in range(1, maximum + 1):
        found = set(range(1, min(total + 1, total & -total)))
        for length in range(1, total.bit_length() + 1):
            found.update(shifted_candidates(total, length))
        direct = {
            x for x in range(1, total + 1)
            if format(x, "b") in format(total + x, "b")
        }
        assert found == direct, total
        pairs += total
    print(f"All {pairs} pairs with 1 <= x <= S <= {maximum} checked by binary substrings.")


def run(steps):
    oeis_prefix = (
        2, 1, 3, 5, 10, 4, 8, 11, 6, 7, 18, 24, 14, 16, 42, 43,
        12, 13, 15, 36, 9, 19, 20, 17, 23, 25, 21, 28, 22, 26,
    )
    total = 2
    used = {2}
    digest = hashlib.sha256(b"2\n")
    first_unused = 1
    max_value = 2
    for index in range(2, steps + 1):
        term = next_term(total, used, first_unused)
        if index <= 2000:
            assert term == direct_next(total, used, first_unused), index
        if index <= len(oeis_prefix):
            assert term == oeis_prefix[index - 1], index
        assert format(term, "b") in format(total + term, "b")
        used.add(term)
        digest.update(f"{term}\n".encode("ascii"))
        max_value = max(max_value, term)
        total += term
        while first_unused in used:
            first_unused += 1
        if index in (1000, 10000, 100000, steps):
            print(f"n={index} sum={total} largest_term={max_value} least_unused={first_unused}")
    assert len(used) == steps
    print(f"SHA-256 of {steps} decimal terms, one per line: {digest.hexdigest()}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--steps", type=int, default=1000000)
    args = parser.parse_args()
    assert args.steps >= 2
    check_offsets(511)
    run(args.steps)
