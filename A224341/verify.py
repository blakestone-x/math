"""Check the two-cycle, its published terms, and bounds on its growth rates."""

from fractions import Fraction
from itertools import combinations


def counts(parts, weight):
    values = [1]
    for n in range(1, weight + 1):
        values.append(sum(values[n - a] for a in parts if a <= n))
    return values


def transform(parts, cap):
    """Exact output through cap when input is known through cap and includes 1,2."""
    assert {1, 2} <= parts
    values = [1]
    for n in range(1, cap + 2):
        value = sum(values[n - a] for a in parts if a <= n)
        if value > cap:
            break
        values.append(value)
    return set(values[1:])


def fixed_supports(cap):
    # Both extreme completions share [1,3] in a given phase. The lemma in
    # the note gives all completions the same prefix after this many steps.
    bound, fib = 3, [0, 1]
    phase_without_three = {1, 2}
    phase_with_three = {1, 2, 3}
    while bound < cap:
        phase_without_three, phase_with_three = (
            transform(phase_with_three, cap),
            transform(phase_without_three, cap),
        )
        while len(fib) <= bound + 2:
            fib.append(fib[-1] + fib[-2])
        bound = fib[bound + 2] - 1
    assert transform(phase_with_three, cap) == phase_without_three
    assert transform(phase_without_three, cap) == phase_with_three
    return phase_without_three, phase_with_three


def direct_compositions(parts, n):
    """Choose cuts between n unit beads, independently of the counting recurrence."""
    total = 0
    for num_cuts in range(n):
        for cuts in combinations(range(1, n), num_cuts):
            breaks = (0, *cuts, n)
            total += all(b - a in parts for a, b in zip(breaks, breaks[1:]))
    return total


def growth_bracket(parts, cap, places):
    """Bracket the zero of sum(lambda**-s) - 1 on an exact decimal grid."""
    scale = 10**places
    lo, hi = scale, 2 * scale
    while hi - lo > 1:
        mid = (lo + hi) // 2
        z = Fraction(scale, mid)
        if sum(z**a for a in parts) > 1:
            lo = mid
        else:
            hi = mid
    z_lo, z_hi = Fraction(scale, lo), Fraction(scale, hi)
    assert sum(z_lo**a for a in parts) > 1
    assert sum(z_hi**a for a in parts) + z_hi**(cap + 1) / (1 - z_hi) < 1
    return lo, hi


def main():
    cap = 150
    a, b = fixed_supports(cap)
    listed_a = [1, 2, 4, 7, 13, 25, 46, 86, 161, 301, 562, 1051, 1964,
                3670, 6859, 12819, 23956, 44772, 83673]
    listed_b = [1, 2, 3, 6, 10, 18, 32, 57, 101, 179, 318, 564, 1002,
                1778, 3157, 5604, 9949, 17661, 31352, 55657]
    assert counts(b, len(listed_a))[1:] == listed_a
    computed_b = counts(a, len(listed_b))[1:]
    differences = [(i, old, new) for i, (old, new) in enumerate(zip(listed_b, computed_b), 1)
                   if old != new]
    assert differences == [(16, 5604, 5603), (17, 9949, 9947), (18, 17661, 17656),
                           (19, 31352, 31342), (20, 55657, 55635)]
    assert direct_compositions(a, 16) == 5603
    for parts in (set(), {1}, {4}, {4, 9}, a, b):
        assert counts(parts, 10)[1:] == [direct_compositions(parts, n) for n in range(1, 11)]
    places = 12
    for label, parts in (("A224341", b), ("A224342", a)):
        lo, hi = growth_bracket(parts, cap, places)
        def decimal(m):
            return f"{m // 10**places}.{m % 10**places:0{places}d}"
        print(f"{label} growth rate lies in ({decimal(lo)}, {decimal(hi)})")
    print("Verified all 19 listed A224341 terms and the first 15 listed A224342 terms.")
    print("A224342 corrections (weight, listed, proved):", differences)


if __name__ == "__main__":
    main()
