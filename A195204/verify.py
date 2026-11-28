"""Compare the shift recurrence, Dyck paths, Hankel factors and permutations."""
from functools import cache
from itertools import permutations
from math import factorial, prod

import sympy as sp


def prefixes(length, alpha):
    current = {0: 1}
    for _ in range(length):
        nxt = {}
        for h, weight in current.items():
            nxt[h+1] = nxt.get(h+1, 0)+weight
            if h:
                nxt[h-1] = nxt.get(h-1, 0)+weight*alpha(h)
        current = nxt
    return current


def polynomial_check():
    a, b, x = sp.symbols("a b x")

    def alpha(h):
        return (a+b)*(x+h//2) if h % 2 else b*(h//2)

    moment = sp.Integer(1)
    for n in range(7):
        assert sp.expand(prefixes(2*n, alpha)[0]-moment) == 0
        moment = sp.expand(x*(a*moment+b*moment.subs(x, x+1)))


def integer_checks(a, b, x):
    total = a+b

    @cache
    def moment(n, y):
        return y*(a*moment(n-1, y)+b*moment(n-1, y+1)) if n else 1

    def alpha(h):
        return total*(x+h//2) if h % 2 else b*(h//2)

    for eps in (0, 1):
        size = 7
        rows = [prefixes(2*i+eps, alpha) for i in range(size)]
        c = sp.Matrix(size, size, lambda i, j: rows[i].get(2*j+eps, 0))
        diag = [total**(j+eps)*b**j*factorial(j)*prod(range(x, x+j+eps))
                for j in range(size)]
        hankel = sp.Matrix(size, size, lambda i, j: moment(i+j+eps, x))
        assert c.det() == 1
        assert c*sp.diag(*diag)*c.T == hankel
    for n in range(8):
        value = 0
        for perm in permutations(range(n)):
            unused = set(range(n))
            cycles = 0
            while unused:
                j = next(iter(unused))
                cycles += 1
                while j in unused:
                    unused.remove(j)
                    j = perm[j]
            exc = sum(v > i for i, v in enumerate(perm))
            value += x**cycles*b**exc*total**(n-exc)
        assert value == moment(n, x)


if __name__ == "__main__":
    polynomial_check()
    for parameters in [(1,1,1), (2,3,5), (-2,5,-3), (-1,1,3), (4,0,2)]:
        integer_checks(*parameters)
    print("Symbolic moments, five specializations of both Hankel forms, and permutation weights passed.")
