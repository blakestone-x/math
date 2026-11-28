"""Integer bounds on the square-array growth constant from a width-20 strip."""
from fractions import Fraction

WIDTH = 20
STEPS = 6


def advance(width, states, counts):
    """Multiply by the full rise-set matrix using the subset-sum transform."""
    last = (1 << (width-1)) - 1
    totals = [0] * (last+1)
    for row in range(1 << width):
        nxt = row >> 1
        rises = (~row & nxt) & last
        drops = (row & ~nxt) & last
        totals[drops] += counts[rises]
    # After the transform, totals[S] sums row weights with drop set contained in S.
    for j in range(width-1):
        half = 1 << j
        for offset in range(0, last+1, 2*half):
            for i in range(offset+half, offset+2*half):
                totals[i] += totals[i-half]
    return {s: totals[last ^ s] for s in states}


def ratio_bounds(width, steps):
    states = [s for s in range(1 << (width-1)) if not (s & (s << 1))]
    current = dict.fromkeys(states, 1)
    for _ in range(steps):
        current = advance(width, states, current)
    following = advance(width, states, current)
    ratios = [Fraction(following[s], current[s]) for s in states]
    return min(ratios), max(ratios)


if __name__ == "__main__":
    low, high = ratio_bounds(WIDTH, STEPS)
    assert low > 306386 and high < 306388
    assert Fraction(1855317,10**6)**(2*(WIDTH+1)) < 2*306386**2
    assert Fraction(1880675,10**6)**WIDTH > 306388
    print("Componentwise certificate: 306386 v < Mv < 306388 v, v = M^6 1.")
    print("The square-array growth constant lies strictly between 1.855317 and 1.880675.")
