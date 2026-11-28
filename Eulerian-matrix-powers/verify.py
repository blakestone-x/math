"""Certify simple negative roots of finite Eulerian matrix powers by exact signs."""
import argparse


def euler_triangle(size):
    rows = [[1]]
    for n in range(1, size + 1):
        last = rows[-1] + [0]
        rows.append([0] + [k * last[k] + (n-k+1) * last[k-1] for k in range(1, n+1)])
    return rows


def multiply(left, right):
    return [[sum(w * right[k][j] for k, w in enumerate(row) if k >= j)
             for j in range(len(row))] for row in left]


def sign_at(coefficients, mantissa, exponent):
    # Evaluate at -mantissa * 2**exponent; all denominator clearings are positive.
    value = coefficients[-1]
    if exponent >= 0:
        for coefficient in reversed(coefficients[:-1]):
            value = coefficient - ((value * mantissa) << exponent)
    else:
        for j, coefficient in enumerate(reversed(coefficients[:-1]), 1):
            value = (coefficient << (-exponent * j)) - value * mantissa
    return (value > 0) - (value < 0)


def certify(row):
    n = len(row) - 1
    assert row[0] == 0 and row[1] > 0 and row[-1] == 1
    q = row[1:]
    for refinement in (1, 2, 4, 8):
        signs = [1]  # sign of q(-z) at z=0
        for octave in range(-2*n-8, 2*n+9):
            target = refinement * (2 + (3*n)//(1+octave*octave))
            bits = (target-1).bit_length()
            for m in range(1 << bits, 2 << bits):
                s = sign_at(q, m, octave-bits)
                if s and s != signs[-1]:
                    signs.append(s)
        end = (-1)**(n-1)
        if signs[-1] != end:
            signs.append(end)   # sign at arbitrarily large z
        if len(signs) == n:
            return n-1
    raise RuntimeError(f'incomplete sign certificate for degree {n}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rows', type=int, default=80)
    parser.add_argument('--power', type=int, default=2)
    args = parser.parse_args()
    if args.rows < 1 or args.power < 1:
        parser.error('rows and power must be positive')
    triangle = euler_triangle(args.rows)
    result = triangle
    for _ in range(1, args.power):
        result = multiply(result, triangle)
    count = 0
    for n, row in enumerate(result[1:], 1):
        count += certify(row)
        if n % 25 == 0:
            print(f'power {args.power}, rows through {n}: {count} distinct negative zeros', flush=True)
    print(f'All {args.rows} rows have simple real zeros, one zero at the origin in each row.')
    print(f'{count} negative zeros certified by rational sign changes.')


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run with Python assertions enabled.')
    main()
