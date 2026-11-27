"""Exact comparisons with Mathar (2013) and OEIS A232622. Requires SymPy."""

import sympy as sp


z = sp.symbols("z")


def equal(name, derived, published):
    if sp.cancel(derived - published) != 0:
        raise AssertionError(name)
    print(name)


def check_dominoes():
    # x marks pairs of columns in the A232622 proof.
    x = z
    letter = x + 2*x/(1-x)
    words = 1/(1-letter)
    orbits = (words + 1/(1-x) + (2+x+letter)*words.subs(x, x**2))/4
    d = (1-x)*(1-4*x+x**2)*(1-4*x**2+x**4)
    equal("A232622", orbits, (1-3*x-4*x**2+10*x**3-4*x**5+x**6)/d)
    equal("A232622 recurrence denominator", d,
          1-5*x+x**2+19*x**3-19*x**4-x**5+5*x**6-x**7)
    equal("Mathar 6", orbits.subs(x, x**2),
          (1/(1+x)+1/(1-x))/8 + (1+2*x**2-x**6)/(2*(1-4*x**4+x**8))
          + (1-x**2)/(4*(1-4*x**2+x**4)))


def bar_series(k):
    h = z**k
    d = 1-z-z*h
    reflected_d = d.subs(z, z**2)
    unrestricted = -h + (1/(1-z-h) + (1+z+h)/(1-z**2-h**2))/2
    zero = -h + ((1+h)/d + (1+z+h+z*h**2)/reflected_d)/2
    one = h**2*(1/d**2 + 1/reflected_d)/2
    return h**2/d**2, h**3*(1-z)/d**3, unrestricted, zero, one


def check_bars():
    l1, l2, _, _, o1 = bar_series(2)
    d = 1-z-z**3
    equal("Mathar 1", l1, z**4/d**2)
    equal("Mathar 2", l2, z**6*(1-z)/d**3)
    equal("Mathar 5", o1, z**4*(1+z+z**2)*(1-z)**2/((1-z**2-z**6)*d**2))

    l1, _, unrestricted, o0, o1 = bar_series(3)
    d = 1-z-z**4
    # For every even t=2j>0, the proof gives h**(j+1)*(1-z)**(j-1)/d**(j+1).
    # Its j=1 term and the ratio of successive terms determine the whole family.
    equal("Mathar 7, first positive class", l1, z**6/d**2)
    equal("Mathar 7, ratio", z**3*(1-z)/d, z**3*(1-z)/(1-z-z**4))
    equal("Mathar 10", unrestricted, -z**3 + (1/(1-z-z**3)
          + (1+z+z**3)/(1-z**2-z**6))/2)
    equal("Mathar 11", o0, -z**3 + ((1+z**3)/d
          + (1+z+z**3+z**7)/(1-z**2-z**8))/2)
    fixed12 = z**2*((1-z)/d**2 - 1/d + z**4/(1-z**2-z**8))/2
    equal("Mathar 12, corrected sign", o1, fixed12)
    printed12 = fixed12 + z**2/d
    equal("Excess in Mathar 12 as printed", printed12 - o1, z**2/d)

    l1, l2, _, o0, o1 = bar_series(4)
    a, b = 1-z+z**2, 1-z**2-z**3
    equal("Mathar 13", l1, z**8/(a*b)**2)
    equal("Mathar 14", l2, z**12*(1-z)/(a*b)**3)
    eq43 = -z**4 + (-(1-3*z-3*z**2+2*z**3)/(1-z**2+z**4) + (3-2*z)/a
           + (8+4*z+5*z**2+6*z**3+3*z**4+5*z**5)/(1-z**4-z**6)
           + (4+6*z+5*z**2)/b)/14
    equal("Mathar 19", o0, eq43)
    eq44 = z**8*(1+z+z**2+z**3+z**4)*(z-1)**2/(
           (z**4-z**2+1)*(1-z**6-z**4)*a**2*b**2)
    equal("Mathar 20", o1, eq44)


if __name__ == "__main__":
    check_dominoes()
    check_bars()
