"""Construct the cycles in the quadratic-label theorem and check their edge labels."""

from argparse import ArgumentParser
from functools import cache
from itertools import permutations
from math import comb, gcd


class Components:
    def __init__(self, size):
        self.parent = list(range(size))
        self.count = size

    def find(self, x):
        while self.parent[x] != x:
            self.parent[x] = self.parent[self.parent[x]]
            x = self.parent[x]
        return x

    def join(self, x, y):
        x, y = self.find(x), self.find(y)
        if x == y:
            return False
        self.parent[y] = x
        self.count -= 1
        return True


def verify_circle(circle):
    n = len(circle)
    residues = set(range(n))
    assert set(circle) == residues
    assert {(x*x + circle[(i+1) % n]) % n for i, x in enumerate(circle)} == residues


def orbit(successor):
    n = len(successor)
    result, x = [], 0
    for _ in range(n):
        result.append(x)
        x = successor[x]
    assert x == 0
    verify_circle(result)
    return tuple(result)


def switch_at_pairs(p, k, ell, t):
    successor = [t] * p
    for x in range(1, (p+1)//2):
        successor[x] = (k*x*x + t) % p
        successor[p-x] = (ell*x*x + t) % p
    assert len(set(successor)) == p
    assert len({(x*x + y) % p for x, y in enumerate(successor)}) == p
    components = Components(p)
    for x, y in enumerate(successor):
        components.join(x, y)
    # The disjoint-set classes start as the cycles. Every accepted edge joins
    # two distinct current cycles, exactly as in the spanning-tree argument.
    for x in range(1, (p+1)//2):
        if components.join(x, p-x):
            successor[x], successor[p-x] = successor[p-x], successor[x]
    return orbit(successor) if components.count == 1 else None


def multipliers(p):
    squares = {x*x % p for x in range(1, (p+1)//2)}
    for k in range(1, p-1):
        ell = p-1-k
        if (k in squares) != (ell in squares):
            return k, ell
    raise AssertionError(f'No multipliers at {p}')


@cache
def prime_circle(p):
    k, ell = multipliers(p)
    for t in range(p):
        circle = switch_at_pairs(p, k, ell, t)
        if circle is not None:
            return circle
    raise AssertionError(f'No connected translation at {p}')


def digit_lift(circle, p):
    m = len(circle)
    successor = [None] * (p*m)
    for i, a in enumerate(circle):
        following = circle[(i+1) % m]
        c = -1 if (2*a+1) % p == 0 or a == 0 else 1
        b = int(i == m-1)
        for y in range(p):
            successor[a + m*y] = following + m*((c*y+b) % p)
    return orbit(successor)


def crt_product(first, second):
    u, v = len(first), len(second)
    inverse = pow(u, -1, v)
    order = []
    for i in range(u*v):
        a, b = first[i % u], second[i % v]
        order.append(a + u*(((b-a)*inverse) % v))
    verify_circle(order)
    return tuple(order)


def factors(n):
    p = 2
    while p*p <= n:
        exponent = 0
        while n % p == 0:
            n //= p
            exponent += 1
        if exponent:
            yield p, exponent
        p += 1
    if n > 1:
        yield n, 1


@cache
def prime_power(p, exponent):
    if exponent == 1:
        return prime_circle(p)
    return digit_lift(prime_power(p, exponent-1), p)


def build_circle(n):
    parts = [prime_power(p, exponent) for p, exponent in factors(n)]
    order = parts[0]
    for part in parts[1:]:
        order = crt_product(order, part)
    return order


def polynomial_value(p, k, ell, d, t):
    """Evaluate the fixed moment obstruction D(t) by its defining recurrence."""
    normalized = [1]
    for r in range(1, d+1):
        right = sum(comb(r, 2*j)*pow(-t, r-2*j, p)*normalized[j]
                    for j in range(r//2+1)) % p
        if r == d:
            return right
        coefficient = (pow(k, r, p) + pow(ell, r, p)) % p
        normalized.append(2*right*pow(coefficient, -1, p) % p)


def check_translations(p):
    squares = {x*x % p for x in range(1, (p+1)//2)}
    witnesses, tested = set(), 0
    pair_count = 0
    for k in range(1, p-1):
        for ell in range(k+1, p-1):
            if (k in squares) == (ell in squares):
                continue
            if (k+1 in squares) == (ell+1 in squares):
                continue
            pair_count += 1
            d = next(r for r in range(1, (p+1)//2)
                     if (pow(k, r, p) + pow(ell, r, p)) % p == 0)
            roots, good = 0, 0
            for t in range(p):
                tested += 1
                value = polynomial_value(p, k, ell, d, t)
                roots += value == 0
                circle = switch_at_pairs(p, k, ell, t)
                if circle is None:
                    assert value == 0
                else:
                    assert circle not in witnesses
                    witnesses.add(circle)
                    good += 1
            assert roots <= d and good >= p-d
    assert pair_count == (p-1)*(p-3)//8
    assert len(witnesses) >= (p*p-1)*(p-3)//16
    return tested


def count_all(n):
    total = 0
    for rest in permutations(range(1, n)):
        circle = (0,) + rest
        labels = {(a*a+circle[(i+1) % n]) % n for i, a in enumerate(circle)}
        total += len(labels) == n
    return total


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--through', type=int, default=3000)
    parser.add_argument('--example', type=int, default=35)
    args = parser.parse_args()
    counts = [count_all(n) for n in range(2, 10)]
    assert counts == [0, 0, 0, 4, 0, 24, 0, 0]
    print('Exact counts for n=2,...,9:', *counts)
    admissible, edges = 0, 0
    for n in range(2, args.through+1):
        square_sum = (n-1)*n*(2*n-1)//6
        if gcd(n, 6) != 1:
            assert square_sum % n != 0
            continue
        verify_circle(build_circle(n))
        admissible += 1
        edges += n
    print(f'All n from 2 through {args.through}: {admissible} verified circles,'
          f' {edges} verified quadratic labels, all other n fail the sum condition.')
    tested = sum(check_translations(p) for p in (5, 7, 11, 13, 17, 19, 23, 29, 31))
    print(f'All {tested} admissible pair/translation choices at primes 5 through 31:'
          ' every disconnected choice is a root of D; both counting bounds hold.')
    n = args.example
    if n < 2 or gcd(n, 6) != 1:
        parser.error('the example modulus must be at least two and coprime to six')
    print(f'Example modulo {n}:', *build_circle(n))


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run Python with assertions enabled.')
    main()
