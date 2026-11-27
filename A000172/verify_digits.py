"""Reproduce the odd-prime support and Eisenstein tests with integer coefficients."""
from bisect import bisect_right
from functools import cache
from math import comb, isqrt


def primes(limit):
    flags = bytearray([1]) * (limit+1)
    flags[:2] = b'\0\0'
    for p in range(2, isqrt(limit)+1):
        if flags[p]:
            flags[p*p::p] = bytes((limit-p*p)//p+1)
    return [p for p, live in enumerate(flags) if live]


@cache
def row(n):
    return [comb(n,j)**2 * comb(2*n-2*j,n) for j in range(n//2+1)]


def digit_product(n,p):
    result = [1]
    place = 1
    while n:
        n,digit = divmod(n,p)
        local = row(digit)
        result2 = [0] * (len(result)+(len(local)-1)*place)
        for j, value in enumerate(local):
            for i, coeff in enumerate(result):
                result2[j*place+i] = value*coeff % p
        result = result2
        place *= p
    return result


def unshifted(n,p):
    if n in (p-1,p-2):
        return True
    power = p
    while (p-1)*power <= n:
        if n in ((p-1)*power, (p-1)*power+1):
            return True
        power *= p
    return False


def value(coefficients,x,m):
    out = 0
    for c in reversed(coefficients):
        out = (x*out+c) % m
    return out


def trim(poly):
    while poly and poly[-1] == 0:
        poly.pop()
    return poly


def remainder(a, b, p):
    a = a.copy()
    leading_inverse = pow(b[-1], -1, p)
    while len(a) >= len(b):
        offset = len(a) - len(b)
        quotient = a[-1] * leading_inverse % p
        for i, coefficient in enumerate(b):
            a[offset + i] = (a[offset + i] - quotient * coefficient) % p
        trim(a)
    return a


def product_mod(a, b, modulus, p):
    if not a or not b:
        return []
    product = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            product[i + j] += x * y
    return remainder(trim([z % p for z in product]), modulus, p)


def power_mod(a, exponent, modulus, p):
    result = [1]
    while exponent:
        if exponent % 2:
            result = product_mod(result, a, modulus, p)
        exponent //= 2
        if exponent:
            a = product_mod(a, a, modulus, p)
    return result


def check_factor_degrees(a, p):
    modulus = trim([z % p for z in row(a)])
    assert len(modulus) == a//2 + 1
    frobenius = [0, 1]
    for j in range(1, 4):
        frobenius = power_mod(frobenius, p, modulus, p)
        difference = frobenius + [0] * max(0, 2-len(frobenius))
        difference[1] = (difference[1] - 1) % p
        f, g = modulus, trim(difference)
        while g:
            f, g = g, remainder(f, g, p)
        assert len(f) == 1, (a, j, f)


def lower_hull_at_23():
    p = 23
    modulus = p**3
    # Horner substitution, one coefficient of f(10+X) at a time.
    shift = []
    for coefficient in reversed(row(1058)):
        next_shift = [coefficient % modulus] + [0] * len(shift)
        for i, v in enumerate(shift):
            next_shift[i] = (next_shift[i] + 10*v) % modulus
            next_shift[i+1] = (next_shift[i+1] + v) % modulus
        shift = next_shift
    hull = []
    for i, coefficient in enumerate(shift):
        if coefficient == 0:
            continue
        v = 0
        while coefficient % p == 0:
            coefficient //= p
            v += 1
        while len(hull) >= 2:
            x, y = hull[-2]
            xx, yy = hull[-1]
            if (xx-x)*(v-yy) > (yy-y)*(i-xx):
                break
            hull.pop()
        hull.append((i, v))
    return hull


def main():
    all_primes = primes(10**7)
    checks = 0
    for p in all_primes[1:]:
        if p>73: break
        for n in range(2,241):
            local = digit_product(n,p)
            actual = row(n)
            assert [c%p for c in actual] == local+[0]*(len(actual)-len(local))
            eis = actual[-1]%p!=0 and actual[0]%(p*p)!=0 and all(c%p==0 for c in actual[:-1])
            assert eis == unshifted(n,p),(n,p)
            checks += 1
    print(f'{checks} entire digit polynomials and unshifted classifications checked.')

    shifted = 0
    for p in all_primes[2:]:
        if p > 79: break
        mod = p*p
        r = -3*pow(2,-1,mod) % mod
        w = ((pow(r,p-1,mod)-1)//p) % p
        t = 1
        while 2*p**t <= 2400:
            n = 2*p**t
            for offset in (0,1):
                expected = w != 0 if offset==0 or t>1 else (2*w+5)%p!=0
                coeffs=row(n+offset)
                const=value(coeffs,r,mod)
                assert const%p == 0 and (const!=0)==expected,(p,t,offset)
                assert value(coeffs,(r+p)%mod,mod)==const
                shifted += 1
            t += 1
    print(f'{shifted} translated constants independently evaluated modulo p squared.')
    wieferich = []
    exceptional_successors = []
    assert len(all_primes) == 664579
    for p in all_primes[2:]:
        modulus = p*p
        r = -3 * pow(2, -1, modulus) % modulus
        w = (pow(r, p-1, modulus)-1)//p
        if w == 0:
            wieferich.append(p)
        if (2*w+5) % p == 0:
            exceptional_successors.append(p)
    assert wieferich == [23] and exceptional_successors == [53047]
    print('664577 primes from 5 to 10000000: W=0 only at 23, 2W+5=0 only at 53047.')

    hull = lower_hull_at_23()
    assert hull == [(0, 2), (23, 1), (529, 0)]
    print('23-adic vertices for f_1058(10+X):', hull)
    for n, expected in ((24334, 24337), (24335, 24337), (106095, 106103)):
        assert all_primes[bisect_right(all_primes, n)] == expected
    assert 106095 == 239 + 128*827 and 827 in all_primes
    for a in (239, 128):
        check_factor_degrees(a, 827)
    print('Three next-prime checks and six polynomial gcd certificates over F_827 passed.')


if __name__=='__main__':
    main()
