"""Exact checks for the single and joint permutation-pattern series. Requires SymPy."""
from collections import Counter
from itertools import permutations
from math import comb

import sympy as sp


def coefficients(formula, u, count):
    """Lagrange inversion for U-1 = x(1+(U-1))(1+2(U-1))."""
    s = sp.Symbol("s")
    num, den = sp.cancel(sp.diff(formula, u).subs(u, 1+s)).as_numer_denom()
    a, b = sp.Poly(num, s), sp.Poly(den, s)
    derivative = []
    for k in range(count):
        subtotal = sum(b.nth(i)*derivative[k-i] for i in range(1, min(k, b.degree())+1))
        derivative.append((a.nth(k)-subtotal)/b.nth(0))
    result = [int(formula.subs(u, 1))]
    for n in range(1, count+1):
        terms = []
        for k in range(n):
            rest = n-1-k
            kernel = sum(comb(n, j)*comb(n, rest-j)*2**j for j in range(rest+1))
            terms.append(derivative[k]*kernel)
        coeff = sum(terms)/n
        assert coeff.is_Integer
        result.append(int(coeff))
    return result


def occurrences(permutation):
    # The second entry of either pattern has one smaller entry to its
    # left and two larger entries to its right, selected independently.
    asc = desc = 0
    for pos, middle in enumerate(permutation):
        left = sum(val < middle for val in permutation[:pos])
        if left == 0:
            continue
        greater = [val for val in permutation[pos+1:] if val > middle]
        for j, val in enumerate(greater):
            for other in greater[j+1:]:
                if val < other:
                    asc += left
                else:
                    desc += left
        if asc+desc > 2:
            break
    return asc, desc


def birth_equations(x, v, g, joint, same):
    """Solve the three source rows in the manuscript as rational identities."""
    u = sp.Symbol("label")
    kernel = 1-(1+x)*u+2*x*u*u
    f1 = (v-1)/v
    f = sp.factor((x*u*(1-u)+x*u*u*f1)/kernel)

    def h(p):
        return sp.factor(sp.diff(p, u).subs(u, 1)-p.subs(u, 1))

    def unrefined(source, root):
        return sp.factor((root-1)*source.subs(u, root)/(x*root**2))

    def refined(source, k, root):
        return sp.factor(((1-u)*source+x*u*u*unrefined(source, root))/k)

    e = 1-2*x*u
    d = h(f)
    b0 = x*x*u*u*d/2
    born = b0/e
    assert sp.factor(unrefined(born, v)-g) == 0
    one = refined(born, kernel, v)
    signed = refined(b0, 1-u+x*u, 1/(1-x))
    mixed_birth = x*x*u*u*h(one-signed)/e + x**4*u*u*d/((1-2*x)*e)
    assert sp.factor(unrefined(mixed_birth, v)-joint) == 0
    fuu = sp.diff(f, u, 2).subs(u, 1)
    same_birth = (x*x*u*u*h(one+signed)/(2*e) + x**3*u*u*fuu/(4*e*e)
                  + x**3*u*u*d*(1+x/(1-2*x))/(2*e))
    assert sp.factor(unrefined(same_birth, v)-same) == 0


def differential_equations(x, u, g):
    n = sp.Symbol("n")
    recurrences = [
        [3*(n+2)*(n-4), -(17*n*n-58*n+75), -3*(n*n-8*n+18), (n-3)*(n-5)],
        [(n-4)*(n+2)*(14*n-37), -6*(14*n**3-86*n*n+185*n-140),
         (n-4)*(n-2)*(14*n-23)],
    ]
    # D=x*d/dx after the rational change of variable x=x(u).
    speed = sp.factor(x/sp.diff(x, u))
    for recurrence in recurrences:
        lhs = 0
        for shift, p in enumerate(recurrence):
            terms = sp.Poly(p.subs(n, n+shift), n).all_coeffs()
            val = terms[0]*g
            for c in terms[1:]:
                val = sp.factor(speed*sp.diff(val, u) + c*g)
            lhs += x**shift*val
        assert sp.cancel(lhs) == 0


def main():
    u = sp.Symbol("u")
    x = (u-1)/(u*(2*u-1))
    g = (u-1)**4/u**2
    joint = 2*(u-1)**6*(2*u-1)*(u*u-u+1)/(u**3*(2*u*u-2*u+1))
    same = (u-1)**5*(2*u**3-u*u+1)/(u**2*(2*u*u-2*u+1))
    radical = 1+x-4*x*u
    assert sp.cancel(radical**2-(1-6*x+x*x)) == 0
    radical_g = (1-10*x+29*x*x-24*x**3+4*x**4
                 -(1-7*x+12*x*x-4*x**3)*radical)/(8*x*x)
    assert sp.cancel(radical_g-g) == 0
    birth_equations(x, u, g, joint, same)
    differential_equations(x, u, g)
    one, mixed, two = [coefficients(f, u, 25) for f in (g, joint, same)]
    assert one[1:] == [
        0,0,0,1,10,71,444,2617,14958,84063,467960,2591265,14308722,
        78911943,435066228,2399404345,13242035030,73150006271,
        404525810928,2239684086529,12415205896794,68905402034311,
        382897019146540,2130255439081721,11865617032955070]
    assert mixed[1:] == [
        0,0,0,0,0,2,32,322,2634,19216,130662,848284,5334332,32788726,
        198201268,1183152686,6995479542,41055940756,239560353258,
        1391435203864,8052418072728,46464481278410,267483032264168,
        1536914425518970,8817393642571330]
    for length in range(10):
        counts = Counter(occurrences(p) for p in permutations(range(length)))
        assert counts[1, 0] == counts[0, 1] == one[length]
        assert counts[1, 1] == mixed[length]
        assert counts[2, 0] == counts[0, 2] == two[length]
    print("Both differential identities, 25 terms in both OEIS tables, and all permutations through length 9 passed.")


if __name__ == "__main__":
    main()
