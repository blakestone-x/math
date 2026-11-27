"""Exact integer checks of the three constructions and the gap-seven obstruction."""
from sympy import jacobi_symbol


def check_blocks(root, place, base, gap):
    left, right = divmod(root*root, place)
    assert place//base <= left <= right < place
    assert right-left == gap


def decimal():
    for n in range(301):
        width = (4*n) % 11
        if width % 2 == 0:
            width += 11
        while 10**width < 2*(n+1)**2:
            width += 22
        for d in (width, width+22):
            place = 10**d
            check_blocks(5*((place+1)//11)+n, place, 10, n*n)
    assert divmod(464**2, 1000) == (215, 296)


def all_bases():
    for b in range(2, 17):
        divisor = 1 if b % 2 == 0 else 2
        p = (b*b+1)//divisor
        for n in range(51):
            length = 2*n*pow(divisor, -1, p) % p
            if length % 2 == 0:
                length += p
            place = b**(2*length)
            while place*(2*p-1) <= p*p*(n+1)**2:
                place *= b**(4*p)
            for block_place in (place, place*b**(4*p)):
                root = (p-1)*((block_place+1)//p)+n
                check_blocks(root, block_place, b, n*n)


def double_squares():
    for n in range(31):
        t = next(t for t in range(1, 585, 8) if (137*t-1980*n) % 73 == 0)
        for width in (t+584, t+1168):
            z = 10**width
            place = z**4
            root = 72*((place+1)//73) + n*(z**3-z)
            check_blocks(root, place, 10, 2*n*n)


def main():
    decimal()
    all_bases()
    double_squares()
    assert 7 not in {x*x % 11 for x in range(11)}
    for a in range(1, 10):
        modulus = 10**(2**a)+1
        assert modulus % 4 == 1 and modulus % 7 in (3, 5)
        assert jacobi_symbol(7, modulus) == -1
    print("All block bounds, identities, and Jacobi checks passed.")


if __name__ == "__main__":
    main()
