"""Integer checks for the least-partner formula and the constructive lifts."""
from collections import Counter
from functools import lru_cache
from itertools import count
from math import prod


@lru_cache(maxsize=None)
def factors(n):
    if n < 1:
        raise ValueError("positive integers only")
    result = {}
    p = 2
    while p*p <= n:
        while n % p == 0:
            result[p] = result.get(p, 0) + 1
            n //= p
        p = p + 1 if p == 2 else p + 2
    if n > 1:
        result[n] = 1
    return result


def divisors(n):
    values = [1]
    for p, e in factors(n).items():
        values = [v*p**i for v in values for i in range(e+1)]
    return sorted(values)


def tau(n):
    return prod(e+1 for e in factors(n).values())


def cores(n):
    mandatory = list(factors(tau(n)).items())

    def visit(i, left, value):
        if i == len(mandatory):
            yield value, left
            return
        q, e = mandatory[i]
        for d in divisors(left):
            if d > e:
                yield from visit(i+1, left//d, value*q**(d-1))

    yield from visit(0, n, 1)


def least(n):
    if n <= 2:
        return 0
    options = []
    for base, left in cores(n):
        if base != n:
            options.append(base)
        elif left > 1:
            q = next(p for p in count(2) if factors(p) == {p:1} and base % p)
            options.append(base*q**(min(factors(left))-1))
    return min(options)


def required_core(n):
    """Pair required prime factors with a budget that leaves minFac(n) free."""
    p = min(factors(n))
    remaining = n // p
    required = [q for q, e in factors(tau(n)).items() for _ in range(e)]
    budget = [v for v, e in factors(remaining).items() for _ in range(e)]
    if len(required) > len(budget):
        assert all(e == 1 for e in factors(n).values())
        return {2:remaining-1}
    groups = Counter()
    for q, v in zip(required, budget):
        groups[q] = (groups.get(q, 1))*v
    first = required[0]
    for v in budget[len(required):]:
        groups[first] *= v
    return {q:d-1 for q,d in groups.items()}


EXPECTED = (
    4,3,16,4,64,24,36,16,1024,6,4096,64,
    4,5,65536,12,262144,6,4,1024,4194304,8,81,4096,
    4,6,268435456,16,1073741824,6,4,65536,16,9,68719476736,262144,
    4,8,1099511627776,32,4398046511104,6,36,4194304,70368744177664,10,729,48,
    4,6,4503599627370496,32,16,8,
)


def main():
    if not __debug__:
        raise RuntimeError("verification requires assertions")
    assert all(least(n) == x for n,x in enumerate(EXPECTED,3))
    assert least(15) == 4 and least(21) == 4 and least(8) == 24 and least(9) == 36
    for n in range(3,1201):
        if len(factors(n)) == 1 and next(iter(factors(n).values())) == 1:
            continue
        exps = required_core(n)
        assert all(exps.get(q,0) >= e for q,e in factors(tau(n)).items())
        assert prod(e+1 for e in exps.values())*min(factors(n)) == n
    # An independent bounded sieve checks every alleged minimum below its limit
    # and checks the absence of a smaller value for the rest.
    bound = 12000
    counts = [0]*(bound+1)
    for d in range(1,bound+1):
        for m in range(d,bound+1,d):
            counts[m] += 1
    for n in range(3,701):
        v = least(n)
        actual = next((k for k in range(counts[n],bound+1,counts[n])
                       if k != n and n % counts[k] == 0),0)
        assert actual == (v if v<=bound else 0)
    print(f"{len(EXPECTED)} published A269781 terms checked")
    print("698 least values tested against a divisor sieve through 12000 (indices 3..700)")
    print("factorized infinite-family witnesses checked at all composite indices 3..1200")


if __name__ == "__main__":
    main()
