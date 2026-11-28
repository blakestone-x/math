"""Integer certificate for the A224294 generating function. Python 3.8+."""
from collections import Counter
from itertools import combinations, permutations
from math import comb

STEP, ONE_LOWER, TWO_OR_MORE = range(3)
START = ((), 0, (), 0, 0)
# Common denominator Q and the three transition numerators in v.
Q = (1, 5, 10, 10, 4)
NUMERATORS = ((0, 1, 2, 2, 0), (0, 0, 1, 0, 0), (0, 0, 0, 1, 1))
P = (1, 12, 78, 332, 1001, 2263, 3998, 5679, 6579, 6213, 4707, 2768, 1192, 336, 48)
OEIS = [0,0,0,0,0,2,34,382,3518,28708,216098,1536960,10488708,69393216,
        448301130,2842611306,17758399872,109613418746,669950441982,4061411038376,
        24453911859134,146393798673526,872121958672162,5173931524573894,30584965562156650]


def close_lower(pending, rank):
    """Each unfinished comparison concerns the first two or three lower ends."""
    inc = rank * sum(weight for size, weight in pending)
    left = tuple((size-1, weight) for size, weight in pending if size > 2)
    return left, inc


def transitions(state):
    ages, previous, pending, total, descending = state
    height = len(ages)
    result = Counter()

    def add(next_ages, last, queries, both, desc, kind=STEP):
        if both > 4 or desc > 2:
            return
        if len(next_ages) == 4:
            next_ages = (3,)*4
        if len(next_ages) < 2 or next_ages[1] != 2:
            last = 0
        target = (next_ages, last, tuple(sorted(queries)), both, desc)
        result[target, kind] += 1

    older = tuple(min(3, a+1) for a in ages)
    if height < 4:
        add(older+(1,), 0, pending, total, descending)
    else:
        # The first one or two lower selections settle all inherited queries.
        for first in (0, 1):
            queries, inc = close_lower(pending, first)
            add(ages, 0, queries, total, descending+inc, ONE_LOWER)
            for second in (0, 1):
                settled, extra = close_lower(queries, second)
                add(ages, 0, settled, total, descending+inc+extra, TWO_OR_MORE)

    if height <= 2:
        added = height*comb(height, 2) if height >= 2 else 0
        queries = pending + (((2, 2),) if added else ())
        add(older, height, queries, total+added, descending)

    for rank in range(min(height, 2)):
        queries, inc = close_lower(pending, rank)
        add(older, rank, queries, total, descending+inc)  # lower level

    for upper_rank in range(min(height, 2)):
        age = ages[upper_rank]
        if upper_rank and age > 2:
            continue
        remaining = older[:upper_rank]+older[upper_rank+1:]
        # None gives an upper level. Each integer choice gives a down step.
        for lower_rank in [None, *range(min(height, 2))]:
            if lower_rank is None:
                next_ages = remaining+(1,)
                queries, inc = pending, 0
            else:
                next_ages = remaining
                queries, inc = close_lower(pending, lower_rank)
            added = upper_rank*comb(upper_rank+age, 2) if upper_rank else 0
            if added:
                inc += (lower_rank or 0) + (previous if age == 2 else 0)
                if len(next_ages) >= 2:
                    queries += ((len(next_ages), 1),)
            add(next_ages, lower_rank or 0, queries, total+added, descending+inc)
    return result


def graph():
    states = [START]
    index = {START: 0}
    edges = []
    for state in states:
        row = []
        for (target, kind), multiplicity in transitions(state).items():
            if target not in index:
                index[target] = len(states)
                states.append(target)
            row.append((index[target], kind, multiplicity))
        edges.append(row)
    final = [int(not ages and total == 4 and desc == 2)
             for ages, _, _, total, desc in states]
    return edges, final


def multiply(a, b):
    out = [0]*(len(a)+len(b)-1)
    for i, u in enumerate(a):
        for j, v in enumerate(b):
            out[i+j] += u*v
    return out


def candidate():
    den = [1, 2]
    for factor in [[1,1]]*5 + [[1,2,2]]*3:
        den = multiply(den, factor)
    return [0]*6+[2*c for c in P], den


def certify():
    edges, final = graph()
    num, den = candidate()
    # Cramer's rule bounds both degrees of each exact solution by 4*N.
    through = 4*len(edges)+max(len(num), len(den))-1
    operators = []
    for i, row in enumerate(edges):
        layers = [Counter({i: -Q[d]}) for d in range(1, 5)]
        for j, kind, weight in row:
            for d in range(1, 5):
                layers[d-1][j] += weight*NUMERATORS[kind][d]
        operators.append([[(j, w) for j, w in layer.items() if w] for layer in layers])
    history = [final]
    series = [final[0]]
    for n in range(1, through+1):
        values = []
        for i, layers in enumerate(operators):
            c = (Q[n]*final[i]) if n <= 4 else 0
            for d in range(1, min(n, 4)+1):
                c += sum(w*history[-d][j] for j, w in layers[d-1])
            values.append(c)
        history = (history+[values])[-4:]
        series.append(values[0])
    for n in range(through+1):
        lhs = sum(den[i]*series[n-i] for i in range(min(n+1, len(den))))
        assert lhs == (num[n] if n < len(num) else 0), n
    return len(edges), through


def ordinary_coefficients(count):
    # v=x(1+v)(1+2v). Evaluate the rational function as a truncated series.
    v = [0]
    for n in range(1, count+1):
        v.append(int(n == 1)+3*v[n-1]+2*sum(v[i]*v[n-1-i] for i in range(1, n-1)))
    def compose(poly):
        result = [0]*(count+1)
        for c in reversed(poly):
            result = multiply(result, v)[:count+1]
            result[0] += c
        return result
    num, den = map(compose, candidate())
    out = []
    for n in range(count+1):
        out.append(num[n]-sum(den[j]*out[n-j] for j in range(1, n+1)))
    return out


def direct(n):
    quads = list(combinations(range(n), 4))
    count = 0
    for perm in permutations(range(n)):
        a = b = 0
        for i,j,k,l in quads:
            if perm[i] < perm[j] < min(perm[k], perm[l]):
                if perm[k] < perm[l]:
                    a += 1
                else:
                    b += 1
                if a > 2 or b > 2:
                    break
        count += (a, b) == (2, 2)
    return count


if __name__ == "__main__":
    size, through = certify()
    coeffs = ordinary_coefficients(28)
    assert coeffs[1:26] == OEIS
    assert coeffs[:9] == [direct(n) for n in range(9)]
    print(f"{size} states. Exact rational identity certified through degree {through} in v.")
    print("All 25 listed terms and direct permutations through length 8 agree.")
    print("Lengths 26, 27, 28:", *coeffs[26:])
