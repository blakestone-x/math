"""Construct every connected translation for one primitive ratio in each tested field."""
from itertools import product
from math import isqrt


def is_prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


class Field:
    """Base-p digits represent polynomial coefficients in increasing order."""

    def __init__(self, p, degree):
        self.q = q = p**degree
        self.p = p
        digits = [[(u // p**j) % p for j in range(degree)] for u in range(q)]
        def pack(coeffs):
            return sum((c % p) * p**j for j, c in enumerate(coeffs))

        self.plus = [[pack(a + b for a, b in zip(digits[u], digits[v]))
                      for v in range(q)] for u in range(q)]
        self.neg = [pack(-a for a in digits[u]) for u in range(q)]
        if degree == 1:
            candidates = ([(g*x) % p for x in range(q)] for g in range(2, p))
        else:
            # Multiplication by X, modulo each candidate monic polynomial.
            candidates = ([pack((([0] + a[:-1])[j] - a[-1]*coeff[j]) for j in range(degree))
                           for a in digits] for coeff in product(range(p), repeat=degree) if coeff[0])
        for step in candidates:
            powers, seen, x = [], set(), 1
            while x and x not in seen:
                powers.append(x)
                seen.add(x)
                x = step[x]
            if x == 1 and len(powers) == q-1:
                break
        else:
            raise ValueError((p, degree))
        # All nonzero residues are powers of X (or g), so the quotient is a field.
        self.powers = powers
        self.log = {u: j for j, u in enumerate(powers)}

    def mul(self, a, b):
        if not a or not b:
            return 0
        return self.powers[(self.log[a] + self.log[b]) % (self.q - 1)]


def construct(field):
    q, add, neg = field.q, field.plus, field.neg
    g = field.powers[1]
    v = neg[field.powers[-field.log[add[g][1]] % (q-1)]]
    u = field.mul(g, v)
    assert add[u][v] == neg[1]
    base = [0] * q
    square = [field.mul(x, x) for x in range(q)]
    pairs = [(x, neg[x]) for x in range(1, q) if x < neg[x]]
    for x, y in pairs:
        base[x], base[y] = field.mul(u, square[x]), field.mul(v, square[x])
    assert len(set(base)) == len({add[square[x]][base[x]] for x in range(q)}) == q
    good = 0
    sample = None
    for t in range(q):
        successor = [add[z][t] for z in base]
        parent = list(range(q))
        def root(i):
            while parent[i] != i:
                parent[i] = parent[parent[i]]
                i = parent[i]
            return i
        for x, y in enumerate(successor):
            parent[root(x)] = root(y)
        for x, y in pairs:
            a, b = root(x), root(y)
            if a != b:
                parent[a] = b
                successor[x], successor[y] = successor[y], successor[x]
        if len({root(x) for x in range(q)}) != 1:
            continue
        path, x = [], 0
        for _ in range(q):
            path.append(x)
            x = successor[x]
        assert x == 0 and len(set(path)) == q and path[1] == t
        labels = [add[square[path[j]]][path[(j+1) % q]] for j in range(q)]
        assert sorted(labels) == list(range(q))
        good += 1
        if sample is None:
            sample = path, labels
    assert good >= (q+1)//2
    return good, sample


if __name__ == "__main__":
    cases = [(p, 1) for p in range(5, 100) if is_prime(p)]
    for p in (3, 5, 7, 11, 13, 17):
        d = 2
        while p**d <= 343:
            cases.append((p, d))
            d += 1
    tried = built = 0
    for p, d in sorted(cases, key=lambda v: v[0]**v[1]):
        field = Field(p, d)
        count, sample = construct(field)
        tried += field.q
        built += count
        if d > 1:
            print(f"F_{p}^{d} (order {field.q}): {count} connected translations; guarantee {(field.q+1)//2}")
        if field.q == 9:
            print("  base-3 coefficient encodings, cycle and labels:", *sample)
    print(f"{len(cases)} fields, {tried} translations tested, {built} cycles constructed and checked.")
