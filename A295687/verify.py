"""Exact rational checks for Bala's series and its Eulerian moment form."""
from fractions import Fraction
from math import factorial


def fibonacci_table(last):
    table = [0, 1]
    while len(table) <= last:
        table.append(table[-1] + table[-2])
    return table


def combinatorial_rows(last):
    stirling = [[1]]
    eulerian = [[], [1]]
    for d in range(1, last + 1):
        prev = stirling[-1] + [0]
        stirling.append([0] + [j * prev[j] + prev[j - 1] for j in range(1, d + 1)])
        if d >= 2:
            prev = [0] + eulerian[-1] + [0]
            eulerian.append([(j + 1) * prev[j + 1] + (d - j) * prev[j] for j in range(d)])
    return stirling, eulerian


def rational_moments(n, h, max_d, fib, stirling):
    """Taylor-expand F_n*x/(1-L_n*x+(-1)^n*x^2) at x=F_h/F_(n+h)."""
    t = fib[n + h]
    x = Fraction(fib[h], t)
    sign = (-1) ** n
    lucas = fib[n-1] + fib[n+1]
    q0 = 1 - lucas*x + sign*x*x
    q1 = -lucas + 2*sign*x
    coeffs = [fib[n]*x/q0]
    for j in range(1, max_d + 1):
        numerator = fib[n] if j == 1 else 0
        previous_two = coeffs[j-2] if j >= 2 else 0
        coeffs.append((numerator - q1*coeffs[j-1] - sign*previous_two)/q0)
    # (x d/dx)^d = sum_j S(d,j) x^j (d/dx)^j.
    return [sum(stirling[d][j] * x**j * factorial(j) * coeffs[j] for j in range(d+1))
            * Fraction(fib[n]**(d+1), t) for d in range(max_d+1)]


def main():
    max_n, max_h, max_d = 60, 14, 8
    fib = fibonacci_table(max_d * max_n + max_h * (max_d + 1))
    stirling, eulerian = combinatorial_rows(max_d)
    a = [1, 2, 2, 1]
    while len(a) <= 2*max_n+7:
        a.append(a[-1] + a[-3] + a[-4])
    count = 0
    for n in range(1, max_n + 1):
        for h in range(2, max_h + 1, 2):
            t = fib[n+h]
            values = rational_moments(n, h, max_d, fib, stirling)
            for d in range(1, max_d + 1):
                rhs = sum(eulerian[d][j] * fib[h]**(j+1) * t**(d-1-j)
                          * fib[(j+1)*n+h*(d+1)] for j in range(d))
                if values[d] != rhs:
                    raise ArithmeticError((n, h, d, values[d], rhs))
                count += 1
            if h == 2 and values[2] != a[2*n+7]:
                raise ArithmeticError(("A295687", n))
    print(f"Verified {count} rational moment identities and {max_n} A295687 identities.")


if __name__ == "__main__":
    main()
