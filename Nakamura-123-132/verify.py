"""Construct Nakamura's polynomials by listing the finite clusters of rank digits."""
from collections import Counter
from fractions import Fraction
from itertools import combinations, permutations
from math import comb, factorial


def cluster_types(budget):
    counts = Counter()

    def extend(prefixes, cost, desc, length):
        if not prefixes and length:
            assert length <= cost+1
            counts[desc, cost-desc, length] += 1
            return
        rank = 0 if length else 2
        while cost+comb(rank, 2) <= budget:
            remaining = []
            added = 0
            for size in prefixes:
                if rank < size:
                    added += rank
                    size -= 1
                if size >= 2:
                    remaining.append(size)
            if rank >= 2:
                remaining.append(rank)
            extend(remaining, cost+comb(rank, 2), desc+added, length+1)
            rank += 1

    extend([], 0, 0, 0)
    return counts


def expansions(budget):
    # Each key (j,L) denotes j ordered clusters using L positions before the final zero.
    clusters = cluster_types(budget)
    forms = {(0, 0): Counter({(0, 0): 1})}
    for cost in range(budget+1):
        for a in range(cost+1):
            b = cost-a
            row = forms.get((a, b), {})
            for (r, s, length), ways in clusters.items():
                if cost+r+s > budget:
                    continue
                nxt = forms.setdefault((a+r, b+s), Counter())
                for (j, used), count in row.items():
                    nxt[j+1, used+length] += count*ways
    return forms


def polynomial(row, n):
    result = Fraction(0)
    for (j, used), ways in row.items():
        arg = n-1-used+j
        # Generalized binomial, also defining the polynomial outside its guaranteed range.
        falling = 1
        for k in range(j):
            falling *= arg-k
        result += Fraction(ways*falling, factorial(j)*2**(1+used))
    return result


def count(row, n):
    if n == 0:
        return int((0,0) in row)
    return sum(ways * 2**(n-1-used) * comb(n-1-used+j, j)
               for (j, used), ways in row.items() if used < n)


def direct(n):
    triples = list(combinations(range(n), 3))
    result = Counter()
    for perm in permutations(range(n)):
        asc = desc = 0
        for i, j, k in triples:
            if perm[i] < min(perm[j], perm[k]):
                if perm[j] < perm[k]:
                    asc += 1
                else:
                    desc += 1
        result[asc, desc] += 1
    return result


def tail_type(values):
    ordered = sorted(values)
    return tuple(ordered.index(v) for v in values)


def longer_counts(n, b, budget):
    """Finite-state count for all b! tail orders. Ranks use complemented values."""
    orders = {p:i for i,p in enumerate(permutations(range(b)))}
    zero = (0,)*len(orders)
    current = {((), 0, zero): 1}
    for pos in range(n):
        future = n-pos-1
        nxt = Counter()
        for (pending, cost, histogram), ways in current.items():
            rank = 0
            while comb(rank,b)+cost <= budget:
                if future < b-1 and rank > future:
                    break
                live, counts = [], list(histogram)
                for values, taken in pending:
                    if rank < len(values):
                        taken += (values[rank],)
                        values = values[:rank]+values[rank+1:]
                    if values:
                        live.append((values,taken))
                    else:
                        for subset in combinations(taken,b):
                            order = tail_type(tuple(-j for j in subset))
                            counts[orders[order]] += 1
                if rank >= b:
                    live.append((tuple(range(rank)), ()))
                nxt[tuple(live), cost+comb(rank,b), tuple(counts)] += ways
                rank += 1
        current = nxt
    return Counter({hist:ways for (pending, _, hist), ways in current.items() if not pending})


def direct_longer(n, b, budget):
    orders = {p:i for i,p in enumerate(permutations(range(b)))}
    positions = list(combinations(range(n), b+1))
    result = Counter()
    for perm in permutations(range(n)):
        hist = [0]*len(orders)
        total = 0
        for pos in positions:
            tail = [perm[i] for i in pos[1:]]
            if perm[pos[0]] < min(tail):
                total += 1
                if total > budget:
                    break
                hist[orders[tail_type(tail)]] += 1
        if total <= budget:
            result[tuple(hist)] += 1
    return result


def main():
    forms = expansions(10)
    assert len(forms) == 66
    for n in range(9):
        enumerated = direct(n)
        for pair, row in forms.items():
            assert count(row, n) == enumerated[pair]
    for (r,s), row in forms.items():
        k = r+s
        lead = sum(Fraction(ways, 2**(1+length)*factorial(j))
                   for (j,length), ways in row.items() if j==k)
        assert lead == Fraction(1, 2**(2*k+1)*factorial(r)*factorial(s))
        for n in range(k+1, k+16):
            assert 2**n*polynomial(row,n) == count(row,n)
    # Nakamura's A224291, whose OEIS offset is 1.
    listed = [0,0,0,0,1,11,60,270,1084,4028,14144,47577,154740,
              489728,1514786,4593118,13682374,40106060,115824376,
              329901232,927585696,2576685888,7076644480,19228648192,51725149184]
    assert [count(forms[4,4],n) for n in range(1,26)] == listed
    for b in (3, 4):
        for n in range(8):
            assert longer_counts(n,b,3) == direct_longer(n,b,3)
    print("66 joint classes checked against every permutation through length 8.")
    print("All leading coefficients and starting indices passed, as did 25 entries of A224291.")
    print("The finite-state construction also matches direct counts at tail sizes 3 and 4 through length 7.")


if __name__ == "__main__":
    main()
