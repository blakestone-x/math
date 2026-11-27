"""Verify the ten slide-line rational identities in Mathar's equations (61)–(72).

Run with Python 3 and SymPy. The inputs on the left of each check are
derived combinatorially in slide-lines.md. The right sides are transcriptions
of the numbered equations. Each test clears polynomial denominators.
"""

from sympy import cancel, symbols


z = symbols("z")
x = z**2
even = 1 / (1 - x)
two_even = (1 - x) / (1 - 3*x + x**2)
two_squared = (1 - z) / ((1 + z)*(1 - 3*z + z**2))
three = (1 - x) / (1 - 4*x + x**2)
four = (1 - x) / (1 - z - 5*x - z**3 + x**2)
two_palindromes_even = (1 + x) / (1 - x - x**2)
three_orbits = (even / 4 + three / 4
                + (1 + 2*x - x**3) / (2*(1 - 4*x**2 + x**4)))
one_line_orbits = (two_even + two_palindromes_even) / 2 - even


def check(number, derived, printed):
    if cancel(derived - printed) != 0:
        raise AssertionError(f"Conjecture {number}: rational functions differ")
    print(f"Conjecture {number} verified.")


check(35, 1 + three - 2*two_even + even,
      1 + 2*x**2 / ((1 - x)*(1 - 4*x + x**2)*(1 - 3*x + x**2)))
check(36, 2*(two_even - even),
      2*x / ((1 - x)*(1 - 3*x + x**2)))
check(37, 2*three + two_squared - 6*two_even + 3*even,
      2*three + (3 - 2*z)/(5*(1 - 3*z + x)) + (17 - 2*z)/(5*(1 - x))
      - 3/(1 - z - x) - 3/(1 + z - x))
check(38, 3*(two_even - even),
      3*x / ((1 - x)*(1 - 3*x + x**2)))
check(39, 1 + four - 2*three - two_squared + 3*two_even - even,
      1 - 2*three - (3 - 2*z)/(5*(1 - 3*z + x)) - (7 - 2*z)/(5*(1 - x))
      + 3/(2*(1 - z - x)) + 3/(2*(1 + z - x)) + four)
check(40, one_line_orbits,
      x*(1 - 2*x) / ((1 - x)*(1 - 3*x + x**2)*(1 - x - x**2)))
check(41, three_orbits - one_line_orbits - x*even,
      1 + three/4 - (1 + x)/(2*(1 - x - x**2)) + even/4
      - 1/(4*(1 - z - x)) - 1/(4*(1 + z - x))
      + (1 + 2*x - x**3)/(2*(1 - 4*x**2 + x**4)))

t = z**3
three_bars = 1 / (1 - z - t)
three_bars_multiple = (1 - t)**2 / ((1 - t)**3 - t)
four_bars = (1 - t)**2 / (1 - 5*t + 3*t**2 - t**3)
check(42, three_bars - t/(1 - t),
      1 + z / ((1 - t)*(1 - z - t)))
check(43, 2*(three_bars_multiple - 1/(1 - t)),
      2*t / ((1 - t)*(1 - 4*t + 3*t**2 - t**3)))
check(44, 1 + four_bars - 2*three_bars_multiple + 1/(1 - t),
      1 + 2*t**2 / ((1 - t)*(1 - 5*t + 3*t**2 - t**3)
                    *(1 - 4*t + 3*t**2 - t**3)))
