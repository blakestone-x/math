"""Exact enumeration of permutations with a fixed number of decreasing triples."""
from collections import Counter, defaultdict
from fractions import Fraction
from functools import cache
from math import comb


def clusters(budget):
    """Count components by (cost, entering height, leaving height, number of steps)."""
    if budget < 0:
        raise ValueError("the occurrence count must be nonnegative")
    inventory = Counter()
    if budget == 0:
        return inventory

    @cache
    def lane(ends):
        older = tuple(age + 1 if age else 0 for age in ends)
        close = []
        for rank, age in enumerate(ends):
            # An unmarked end closes first. A marked end must pay positive cost.
            if not ((rank == 0 and age == 0) or (rank > 0 and age > 0)):
                continue
            cost = rank * (rank + age)
            if cost <= budget:
                close.append((older[:rank] + older[rank + 1:], cost))
        return older, close

    @cache
    def outstanding(ends):
        # A marked end cannot regain a lost rank. Age + rank never decreases.
        if ends and ends[0]:
            return budget + 1
        return sum(rank + age for rank, age in enumerate(ends) if age)

    @cache
    def steps(upper, lower):
        # An age of zero denotes an ordinary end. Positive ages mark ends
        # that must eventually close at a positive rank.
        u, close_u = lane(upper)
        v, close_v = lane(lower)
        result = [(u, v, len(u)**2)]  # fixed point
        for left in (0, 1):
            for right in (0, 1):
                result.append((u + (left,), v + (right,), 0))
        for end_u, cu in close_u:
            for mark in (0, 1):
                result.append((end_u + (mark,), v, cu))
            for end_v, cv in close_v:
                result.append((end_u, end_v, cu + cv))
        for end_v, cv in close_v:
            for mark in (0, 1):
                result.append((u, end_v + (mark,), cv))
        return [(u, v, cost, outstanding(u) + outstanding(v))
                for u, v, cost in result
                if cost + outstanding(u) + outstanding(v) <= budget]

    for start in range(budget + 1):
        plain = (0,) * start
        layer = Counter({(plain, plain, 0): 1})
        for length in range(1, budget + 1):
            following = Counter()
            for (upper, lower, spent), count in layer.items():
                for u, v, extra, pending in steps(upper, lower):
                    cost = spent + extra
                    if cost + pending > budget:
                        continue
                    if pending:
                        following[u, v, cost] += count
                    elif cost:
                        inventory[cost, start, len(u), length] += count
            layer = following
            if not layer:
                break
        assert not layer
    assert all(v == inventory[k, b, a, l] and max(a, b, l) <= k
               for (k, a, b, l), v in inventory.items())
    return inventory


def multiply(p, q):
    if not p or not q:
        return []
    result = [0] * (len(p) + len(q) - 1)
    for i, c in enumerate(p):
        if c:
            for j, d in enumerate(q):
                result[i + j] += c * d
    return result


def add_to(p, q, shift=0, scale=1):
    p.extend([0] * max(0, len(q) + shift - len(p)))
    for j, c in enumerate(q, shift):
        p[j] += c * scale


def catalan_numerators(budget, inventory):
    """Return V_r(u) = (1+u)^(2r) F_r(u/(1+u)^2) for 0 <= r <= budget."""
    starts = defaultdict(list)
    for (cost, a, b, length), count in inventory.items():
        degree = 2 * (cost - length)
        weight = [count * comb(degree, i) for i in range(degree + 1)]
        starts[cost, a].append((b, length, weight))
    green = {(h, a): multiply([1, 1], [0] * abs(h-a) + [1] * (2 * min(h, a)+1))
             for h in range(budget + 1) for a in range(budget + 1)}
    previous = [[[0] * h + [1, 1] for h in range(budget + 1)]]
    for r in range(1, budget + 1):
        responses = [[] for _ in range(r + 1)]
        for cost in range(1, r + 1):
            for a in range(cost + 1):
                for b, length, weight in starts[cost, a]:
                    add_to(responses[a], multiply(weight, previous[r-cost][b]), length)
        current = []
        for h in range(budget + 1):
            result = []
            for a, response in enumerate(responses):
                if response:
                    add_to(result, multiply(green[h, a], response))
            current.append(result)
        previous.append(current)
    return [entry[0] for entry in previous]

def radical_pair(r, numerator):
    """P, Q in 2*x^(2r+1)*F_r = P + Q*sqrt(1-4x), in ascending powers."""
    d = 2*r + 1
    trace = [[2], [1]]
    divided_difference = [[], [1]]
    for sequence in (trace, divided_difference):
        for _ in range(2, 6*r + 3):
            nxt = sequence[-1].copy()
            add_to(nxt, sequence[-2], shift=1, scale=-1)
            sequence.append(nxt)

    p, q = [], []
    for j, coefficient in enumerate(numerator):
        if coefficient:
            a, b = d + j, d + 2*r - j
            assert min(a, b) >= 0
            degree = abs(a-b)
            add_to(p, trace[degree], shift=min(a,b), scale=coefficient)
            if a != b:
                sign = 1 if b > a else -1
                add_to(q, divided_difference[degree], shift=min(a,b), scale=sign*coefficient)
    for poly in (p, q):
        while poly and not poly[-1]:
            poly.pop()
    return p, q


@cache
def catalan(n):
    return comb(2*n, n) // (n+1)


def coefficient(r, p, q, n):
    """Coefficient of length n, including the polynomial part at short lengths."""
    k = n + 2*r + 1
    polynomial = (p[k] if k < len(p) else 0) + (q[k] if k < len(q) else 0)
    assert polynomial % 2 == 0
    return polynomial // 2 - sum(c * catalan(k-i-1) for i, c in enumerate(q[:k]))


def records(limit):
    result = []
    for r, numerator in enumerate(catalan_numerators(limit, clusters(limit))):
        p, q = radical_pair(r, numerator)
        amplitude = Fraction(sum((j-r)*c for j, c in enumerate(numerator)), 4**r)
        result.append({"r": r, "P": p, "Q": q, "amplitude": str(amplitude)})
    return result


if __name__ == "__main__":
    import argparse
    import json

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("r", type=int, help="number of decreasing triples")
    parser.add_argument("--terms", type=int, metavar="N", help="also give counts from length zero through N")
    args = parser.parse_args()
    if args.r < 0 or (args.terms is not None and args.terms < 0):
        parser.error("r and N must be nonnegative")
    data = records(args.r)[-1]
    if args.terms is not None:
        data["counts"] = [coefficient(args.r, data["P"], data["Q"], n)
                          for n in range(args.terms + 1)]
    print(json.dumps(data, indent=2))
