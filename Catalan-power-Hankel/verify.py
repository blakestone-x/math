"""Exact checks using the original moment matrices, without Chebyshev polynomials."""

from functools import cache
from math import comb


@cache
def moment(power, index):
    if index < 0:
        return 0
    return power * comb(2 * index + power, index) // (2 * index + power)


def determinant(matrix):
    """Bareiss elimination including row swaps and singular matrices."""
    n = len(matrix)
    sign, previous = 1, 1
    if not n:
        return 1
    for j in range(n - 1):
        pivot = next((i for i in range(j, n) if matrix[i][j]), None)
        if pivot is None:
            return 0
        if pivot != j:
            matrix[j], matrix[pivot] = matrix[pivot], matrix[j]
            sign = -sign
        row = matrix[j]
        for i in range(j + 1, n):
            target = matrix[i]
            for k in range(j + 1, n):
                numerator = row[j] * target[k] - target[j] * row[k]
                target[k], remainder = divmod(numerator, previous)
                assert not remainder
        previous = row[j]
    return sign * matrix[-1][-1]


def verify():
    counts = [0, 0, 0]
    for k in range(1, 8):
        for odd in (False, True):
            power = 2 * k - int(odd)
            h = power if odd else k
            epsilon = (-1) ** (k - 1 if odd else comb(k, 2))
            for shift in range(1 - k, 7):
                a = k + shift - int(odd)
                d = a + k - 1
                e0 = 1 + comb(a, 2)
                source_e = 1 + comb(k + shift, 2)
                exponents = [e for e in sorted({e0, source_e}) if h * e <= 40]
                if not exponents:
                    continue
                limit = h * max(exponents) + max(h, 4)
                values = [determinant([[moment(power, i + j + shift)
                                        for j in range(n)] for i in range(n)])
                          for n in range(limit + 1)]
                counts[0] += 1
                counts[1] += len(values)
                for exponent in exponents:
                    multiplier = [comb(exponent, i) * (-epsilon) ** i
                                  for i in range(exponent + 1)]
                    numerator = [sum(multiplier[j] * values[n - j * h]
                                     for j in range(min(n // h, exponent) + 1))
                                 for n in range(limit + 1)]
                    degree = h * exponent - d if d else exponent - 1
                    sign = (-(-epsilon) ** exponent * (-1) ** comb(d, 2)
                            if d else (-1) ** (exponent - 1))
                    assert numerator[0] == 1 and not any(numerator[degree + 1:])
                    assert numerator[:degree + 1] == [
                        sign * c for c in reversed(numerator[:degree + 1])]
                    if exponent == source_e:
                        even_pal = ({1, 3}, {0, 1, 2, 3}, {0, 3}, {1, 2})
                        odd_pal = ({0, 1}, {0, 2}, {0, 1}, {1, 3})
                        expected = shift % 4 in (odd_pal if odd else even_pal)[k % 4]
                        assert expected == (sign == 1)
                    counts[2] += 1
    print(f"power and shift pairs {counts[0]}")
    print(f"original integer Hankel determinants computed {counts[1]}")
    print(f"numerators checked for degree, reciprocity and zero tail {counts[2]}")
    print("all exact checks passed")



def multiply(left, right):
    result = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            result[i + j] += a * b
    return result


def sparse(terms):
    result = [0] * (1 + max(index for index, _ in terms))
    for index, value in terms:
        result[index] += value
    return result


def check_low_shifts():
    families = 0
    for k in range(3, 10):
        s = lambda j: (-1) ** comb(j, 2)
        for odd in (False, True):
            power = 2 * k - int(odd)
            h = power if odd else k
            epsilon = (-1) ** (k - 1) if odd else s(k)
            u = sparse([(0, 1), (h, -epsilon)])
            for level in (1, 2, 3):
                shift = level - k
                if level == 1:
                    expected = sparse([(0, 1), (k, s(k))]) if odd else [1]
                elif level == 2:
                    expected = sparse([(0, 1), (k - 1, s(k - 1))])
                    if odd:
                        expected = multiply(expected, u)
                elif odd:
                    expected = multiply(sparse([(0, 1), (k - 2, s(k - 2))]), u)
                    expected[k - 1] += (2 * k - 1) * s(k - 1)
                    expected[2 * k - 2] += 2 * k - 1
                    expected = multiply(multiply(expected, u), u)
                else:
                    expected = multiply(sparse([(0, 1), (k - 2, s(k - 2))]),
                                        sparse([(0, 1), (2 * k, -1)]))
                    expected[k - 1] += s(k - 1) * k ** 2
                    expected[2 * k - 1] += s(k - 1) * s(k) * k ** 2
                exponent = 1 + comb(level, 2)
                # Produce input coefficients from the claimed rational expression,
                # then compare with actual determinants even beyond numerator degree.
                coefficients = []
                for n in range(len(expected) + 3):
                    value = expected[n] if n < len(expected) else 0
                    for j in range(1, min(n // h, exponent) + 1):
                        value -= comb(exponent, j) * (-epsilon) ** j * coefficients[n - j * h]
                    coefficients.append(value)
                    actual = determinant([[moment(power, i + j + shift)
                                           for j in range(n)] for i in range(n)])
                    assert value == actual, (k, odd, level, n)
                families += 1
    print(f"explicit low-shift numerator formulas checked {families}")


if __name__ == "__main__":
    verify()
    check_low_shifts()
