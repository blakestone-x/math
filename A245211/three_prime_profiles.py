"""Print every ordered exponent profile passing the local unit tests."""
from functools import lru_cache
from math import gcd

MODULI = (8, 16, 32, 64, 3, 9, 27, 81, 5, 25, 7, 49,
          11, 13, 17, 19, 23, 29, 31, 37, 41, 43)


def residues(modulus, highest):
    units = [x for x in range(modulus) if gcd(x, modulus) == 1]
    geometric = [1] * len(units)
    moment = [1] * len(units)
    result = [(1,)]
    for _ in range(highest):
        for i, x in enumerate(units):
            geometric[i] = (1 + x * geometric[i]) % modulus
            moment[i] = (moment[i] + geometric[i]) % modulus
        result.append(tuple(sorted(set(moment))))
    return result


def exponent_profiles(c):
    triples = [(a, b, c) for b in range(c, 10*c + 8)
               for a in range(b, (3*c + 4)*b + 3*c + 1)]
    for m in MODULI:
        values = residues(m, max(a for a, _, _ in triples))

        @lru_cache(maxsize=None)
        def products(left, right):
            pair = {x*y % m for x in left for y in right}
            return {z*w % m for z in pair for w in values[c]}

        survivors = []
        for a, b, c in triples:
            D = (a+1)*(b+1)*(c+1)
            if 2*m >= D or (D+1) % m in products(values[a], values[b]):
                survivors.append((a, b, c))
        products.cache_clear()
        triples = survivors
    return triples


def check_four_equal():
    def moments(e, m):
        return {sum((t+1)*pow(x,t,m) for t in range(e+1)) % m
                for x in range(1,m) if gcd(x,m)==1}
    # H and F differ by an e-th power of the base. Compute normalized
    # residues in the case where the actual nonzero values matter.
    mod7 = {sum((10-t)*pow(x,t,7) for t in range(10)) % 7 for x in range(1,7)}
    if mod7 != {0,5,6} or 0 in moments(21,73) or (22**4+1) % 73 != 0:
        raise ArithmeticError('The four-equal local tables do not agree.')


if __name__ == '__main__':
    check_four_equal()
    for least, count in [(4, 502), (6, 324), (8, 5849), (9, 13779)]:
        profiles = exponent_profiles(least)
        if len(profiles) != count:
            raise ArithmeticError((least, len(profiles)))
        for triple in profiles:
            print(*triple)
