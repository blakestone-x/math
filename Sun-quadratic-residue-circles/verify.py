"""Exact finite-field cyclic square-label tests. Uses only the Python standard library."""
from collections import Counter
from functools import lru_cache
from itertools import product
from math import gcd, isqrt


def prime_factors(n):
    factors = []
    for divisor in range(2, isqrt(n) + 1):
        if n % divisor == 0:
            factors.append(divisor)
            while n % divisor == 0:
                n //= divisor
    if n > 1:
        factors.append(n)
    return factors


def monic_remainder(dividend, divisor, p):
    values = list(dividend)
    m = len(divisor) - 1
    for i in range(len(values) - 1, m - 1, -1):
        c = values[i]
        for j, a in enumerate(divisor):
            values[i - m + j] = (values[i - m + j] - c * a) % p
    return values[:m]


def irreducible_modulus(p, degree):
    if degree == 1:
        return (0, 1)
    divisors = [coeff + (1,) for j in range(1, degree // 2 + 1)
                for coeff in product(range(p), repeat=j) if coeff[0]]
    for coeff in product(range(p), repeat=degree):
        polynomial = coeff + (1,)
        if coeff[0] and all(any(monic_remainder(polynomial, h, p)) for h in divisors):
            return polynomial
    raise AssertionError('irreducible polynomial not found')


class Field:
    def __init__(self, p, degree):
        self.p = p
        self.degree = degree
        self.q = p**degree
        self.polynomial = irreducible_modulus(p, degree)
        self.digits = [tuple((x // (p**i)) % p for i in range(degree))
                       for x in range(self.q)]

    def encode(self, coefficients):
        return sum((x % self.p) * self.p**j for j, x in enumerate(coefficients))

    def add(self, x, y, sign=1):
        return self.encode([a+sign*b for a, b in zip(self.digits[x], self.digits[y])])

    def multiply(self, x, y):
        if self.degree == 1:
            return x*y % self.p
        result = [0]*(2*self.degree-1)
        for i, a in enumerate(self.digits[x]):
            for j, b in enumerate(self.digits[y]):
                result[i+j] += a*b
        return self.encode(monic_remainder(result, self.polynomial, self.p))

    def power(self, x, exponent):
        value = 1
        while exponent:
            if exponent % 2:
                value = self.multiply(value, x)
            x = self.multiply(x, x)
            exponent //= 2
        return value

    def powers_of_generator(self):
        factors = prime_factors(self.q-1)
        for x in range(1, self.q):
            if all(self.power(x, (self.q-1)//h) != 1 for h in factors):
                powers = [1]
                for _ in range(self.q-2):
                    powers.append(self.multiply(powers[-1], x))
                assert len(set(powers)) == self.q-1 and self.multiply(powers[-1], x) == 1
                return powers
        raise AssertionError('generator not found')


def geometric_and_direct(field):
    powers = field.powers_of_generator()
    squares = powers[::2]
    nonsquares = powers[1::2]
    n = len(squares)
    rows = []
    for sign in (1, -1):
        for square_target in (True, False):
            target = set(squares if square_target else nonsquares)
            witness = next((j for j in range(n) if gcd(j, n) == 1 and
                            field.add(1, squares[j], sign) in target), None)
            if witness is not None:
                circle = [squares[(witness*i) % n] for i in range(n)]
                labels = {field.add(circle[i], circle[(i+1) % n], sign) for i in range(n)}
                assert len(set(circle)) == n and labels == target
                rows.append((sign, square_target, 'geometric'))
            else:
                assert n <= 20
                count = count_circles(field, squares, target, sign)
                rows.append((sign, square_target, count))
    return rows


def count_circles(field, squares, target, sign):
    # State = used vertex mask, used label mask, current vertex. Fix first vertex 1.
    n = len(squares)
    indices = {x:i for i, x in enumerate(sorted(target))}
    adjacency = [[(j, 1 << indices[value]) for j, y in enumerate(squares)
                  if (value := field.add(x, y, sign)) in indices] for x in squares]

    @lru_cache(maxsize=None)
    def extend(vertices, labels, pos):
        if vertices == (1 << n)-1:
            return sum(1 for j, bit in adjacency[pos] if j == 0 and not labels & bit)
        return sum(extend(vertices | (1 << j), labels | bit, j)
                   for j, bit in adjacency[pos] if not vertices & (1 << j) and not labels & bit)
    return extend(1, 0, 0)


def main():
    counts = Counter()
    failures = {case:[] for case in product((1,-1), (True,False))}
    unresolved = []
    fields = 0
    for p in range(3, 1026, 2):
        if prime_factors(p) != [p]:
            continue
        degree = 1
        while p**degree <= 1025:
            field = Field(p, degree)
            fields += 1
            for sign, square_target, status in geometric_and_direct(field):
                counts['geometric' if status == 'geometric' else 'enumerated'] += 1
                if status != 'geometric':
                    unresolved.append((field.q,sign,square_target,status))
                if status == 0:
                    failures[sign,square_target].append(field.q)
            degree += 1
    print(f'{fields} odd finite fields, {(4*fields)} target/sign cases.')
    print(f'{counts["geometric"]} certified by geometric cycles; {counts["enumerated"]} by exact enumeration.')
    print('Cases without a generator witness (q : sum/difference, target, based cycle count):')
    for q,sign,square,c in sorted(unresolved):
        print(q, '+' if sign==1 else '-', 'S' if square else 'T', c)
    print('Complete failure lists:')
    for (sign,square),fail in failures.items():
        print('+' if sign==1 else '-', 'S' if square else 'T', sorted(fail))


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run with assertions enabled.')
    main()
