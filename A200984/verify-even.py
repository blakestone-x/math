"""Exact certificates for the Fourier coefficients in the even-alphabet proof."""
from math import comb

from sympy import Poly, QQ, symbols

from verify import arrays, differences


def scaled_density(i):
    """The centered uniform-sum density times 2^(i-1) (i-1)!."""
    return sum((-1)**h * comb(i, h) * (i - 2*h)**(i-1)
               for h in range((i+1)//2))


def missing_poles(q, z):
    # Compute the even coefficients of D directly, without complex numbers.
    coeffs = [0] * (q+1)
    for i in range(1, q, 2):
        weight = comb(q, i) * scaled_density(i) * scaled_density(q-i)
        for h in range(i+1):
            signed = weight * (-1)**h * comb(i, h)
            for k in range(q-i+1):
                coeffs[h+k] += signed * comb(q-i, k)
    assert not any(coeffs[1::2])
    assert coeffs[-1] == -coeffs[0]
    p = Poly.from_list(coeffs[:-1:2][::-1], z, domain=QQ)
    roots = Poly(1 + z**(q//2), z, domain=QQ)
    return p.gcd(roots).degree()


def main():
    z = symbols("z")
    required = [missing_poles(q, z) for q in range(2, 17, 2)]
    assert required == [0]*8
    assert all(missing_poles(q, z) == 0 for q in range(18, 33, 2))
    q = z+6
    difference = 25*(q-3)**3*q**4 - (q-1)**3*(5*q**2-27*q+54)**2
    assert Poly(difference, z).all_coeffs() == [
        120, 2841, 27313, 135411, 360315, 475200, 226800]
    for q in (10, 12):
        # Recover the entire rational function independently by enumerating
        # column assignments and interpolating each degree-(q-1) constituent.
        numerator = [0]*(q*q)
        for s in range(q):
            samples = [arrays(q, q*m+s) for m in range(q)]
            for i, delta in enumerate(differences(samples)):
                for j in range(q-i):
                    numerator[s+q*(i+j)] += delta*(-1)**j*comb(q-1-i, j)
        num = Poly.from_list(numerator[::-1], z, domain=QQ)
        den = Poly((1-z**q)**q, z, domain=QQ)
        reduced = den.exquo(den.gcd(num)).monic()
        expected = Poly((1-z**(q//2))*(1-z**q)**(q-1), z, domain=QQ)
        assert reduced == expected.monic()
    print("Required gcd degrees:", required)
    print("Checks through q=32, the bound polynomial, and direct denominators for q=10,12 passed.")


if __name__ == "__main__":
    main()
