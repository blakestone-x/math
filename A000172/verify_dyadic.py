"""Verify the finite Newton polygons and prime gaps in the dyadic-ray theorem."""
from array import array
from functools import lru_cache
from math import comb, isqrt
import sys

MAX_ODD_PART = 127
DUSART_START = 396738


def v2(n):
    if n <= 0:
        raise ValueError("a positive integer is required")
    return (n & -n).bit_length() - 1


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def next_prime(n):
    q = n + 1
    while not prime(q):
        q += 1
    return q


def hull(points):
    result = []
    for x, y in points:
        while len(result) >= 2:
            (a, h), (b, k) = result[-2:]
            if (k-h)*(x-b) < (y-k)*(b-a):
                break
            result.pop()
        result.append((x, y))
    return result


def degree_exponent(polygon):
    """Every factor degree is divisible by 2**max(0, this number)."""
    return min(v2(b-a) - v2(abs(k-h))
               for (a, h), (b, k) in zip(polygon, polygon[1:]))


def shifted_polygon(b, t, precision, offset=0):
    n = (b << t) + offset
    d = n // 2
    s = n.bit_count()
    leading = d.bit_count() + (d+1).bit_count() if offset else 2*s
    modulus = 1 << precision
    mask = modulus - 1
    odd_factorial = array('I', [1])
    for i in range(1, 2*n+1):
        odd_factorial.append(odd_factorial[-1] * (i >> v2(i)) & mask)

    @lru_cache(None)
    def inverse(unit):
        return pow(unit, -1, modulus)

    def binomial_unit(n, k):
        denominator = odd_factorial[k] * odd_factorial[n-k] & mask
        return odd_factorial[n] * inverse(denominator) & mask

    # Store the coefficients of f_n that survive the chosen precision.
    # Each term with j>0 has valuation at least s+t-1-v2(j).
    stride = 1 << max(0, s+t-precision)
    coefficients = []
    for j in range(0, d+1, stride):
        valuation = (2*j.bit_count() + (n-2*j).bit_count()
                     + (n-j).bit_count() - s)
        if valuation < precision:
            odd = binomial_unit(n, 2*j) * binomial_unit(2*j, j)
            odd *= binomial_unit(2*n-2*j, n-j)
            coefficients.append((j, odd << valuation & mask, valuation))

    value_at_one = sum(c for _, c, _ in coefficients) & mask
    if value_at_one == 0 or leading >= precision:
        return None
    top = max(v2(value_at_one), leading)
    # Both endpoints have height <= top; higher coefficients cannot be vertices.
    # The same valuation bound holds after X -> 1+X.
    stride = 1 << max(0, s+t-1-top)
    low_points = []
    for i in range(0, d+1, stride):
        total = 0
        for j, coefficient, valuation in coefficients:
            if j < i:
                continue
            extra = i.bit_count() + (j-i).bit_count() - j.bit_count()
            if valuation + extra <= top:
                total += coefficient * binomial_unit(j, i) << extra
        total &= (1 << (top+1)) - 1
        if total:
            low_points.append((i, v2(total)))
    polygon = hull(low_points)
    assert polygon[0][0] == 0 and polygon[-1] == (d, leading)
    assert all(h != k for (_, h), (_, k) in zip(polygon, polygon[1:]))
    return polygon


def check_direct():
    # Independent, full polynomial translation using arbitrary-size integers.
    for n in [*range(2, 99, 2), *range(3, 128, 2)]:
        offset = n % 2
        t = v2(n-offset)
        b = (n-offset) >> t
        coefficients = [comb(n, j)**2 * comb(2*n-2*j, n) for j in range(n//2+1)]
        shifted = [sum(coefficients[j]*comb(j, i) for j in range(i, len(coefficients)))
                   for i in range(len(coefficients))]
        expected = hull((i, v2(x)) for i, x in enumerate(shifted))
        precision = max(v2(shifted[0]), v2(shifted[-1])) + 1
        assert shifted_polygon(b, t, precision, offset) == expected


def verify():
    check_direct()
    counts = [[0, 0, 0], [0, 0, 0]]
    largest_ratio = 0
    print('odd_part base_exponent loss')
    for b in range(1, MAX_ODD_PART+1, 2):
        # The first t at which both endpoint heights fit at absolute precision t+1.
        # This loop terminates by the explicitly checked bound 14 in the table.
        for base in range(max(1, 2*b.bit_count()), 15):
            polygon = shifted_polygon(b, base, base+1)
            if polygon is not None:
                break
        else:
            raise AssertionError(('missing base for ray', b))
        loss = base - degree_exponent(polygon)
        assert loss >= 0
        largest_ratio = max(largest_ratio, b << loss)
        print(b, base, loss, flush=True)
        for offset in (0, 1):
            threshold = base + 2*offset
            # t=0 at a successor is already an even index with n<=128.
            for t in range(offset, max(threshold, DUSART_START.bit_length())+1):
                n = (b << t) + offset
                if n >= DUSART_START and t >= threshold:
                    break
                if n < 2:
                    continue
                if n <= 2048 or any(prime(n+i) for i in (-1, 0, 1, 2)):
                    counts[offset][0] += 1
                    continue
                assert t >= 1
                if t >= threshold:
                    exponent = t - loss
                    counts[offset][2] += 1
                else:
                    d = n//2
                    leading = d.bit_count()+(d+1).bit_count() if offset else 2*b.bit_count()
                    precision = max(t+1, leading+1)
                    local = shifted_polygon(b, t, precision, offset)
                    while local is None:
                        precision += 1
                        local = shifted_polygon(b, t, precision, offset)
                    exponent = degree_exponent(local)
                    counts[offset][1] += 1
                bound = 1 << max(0, exponent)
                assert (next_prime(n)-1-offset-n)//2 < bound, (b, t, n, bound)
            else:
                raise AssertionError(('infinite tail not reached', b, offset))
    assert largest_ratio == 888
    print('Maximum b times 2**loss:', largest_ratio)
    for offset, (prior, direct, lift) in enumerate(counts):
        print(f'Offset {offset}: {prior} by earlier theorems, {direct} by direct polygon, {lift} by dilation.')
    print('Independent full translations agree at 49 even and 63 odd indices.')


if __name__ == '__main__':
    if not __debug__:
        sys.exit('Run with Python assertions enabled.')
    verify()
