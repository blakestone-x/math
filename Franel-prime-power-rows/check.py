"""Direct binomial checks for the general formulas, using Python integers."""
from math import comb


def vp(n, prime):
    result = 0
    while n % prime == 0:
        n //= prime
        result += 1
    return result


def main():
    odd_checks = 0
    for p in (3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43):
        q = 1
        while p**q <= 1600:
            n = p**q - 1
            row = [1]
            for i in range(1, n+1):
                row.append(row[-1]*(n+1-i)//i)
            # These include pairs of different parity and deep p-adic differences.
            for s in (1, 2, 3, 7):
                for delta in (1, 2, p, 2*p, p*p, p**3):
                    r = s+delta
                    modulus = p**(q+1+vp(delta,p))
                    total = sum((-1 if k*r % 2 else 1)*pow(v,r,modulus)
                                - (-1 if k*s % 2 else 1)*pow(v,s,modulus)
                                for k,v in enumerate(row))
                    assert (total + p**q*delta) % modulus == 0
                    odd_checks += 1
            q += 1
    print(f"{odd_checks} signed odd-prime difference congruences passed.")

    comparisons = 0
    for q in range(4, 12):
        n = 2**q - 1
        row = [comb(n,k) for k in range((n+1)//2)]
        h = 3*q-3
        for m in range(1, 3*q+1):
            modulus = 1 << (m+h+3)
            delta = (2*sum(pow(b,1+(1<<m),modulus) for b in row) - pow(2,n,modulus)) % modulus
            assert delta == (1 if m == 1 else 7 if m == 2 else 3) << (m+h)
            comparisons += 1
    print(f"{comparisons} binary residues checked by exact combinations and modular powers.")
    q, m = 5, 19
    modulus = 1 << 34
    residue = sum(pow(comb(31,k),2**m+1,modulus) for k in range(32)) % modulus
    assert residue == 1 << 33
    print(f"q={q}, m={m}: residue modulo 2^34 = {residue}; valuation = 33.")


if __name__ == '__main__':
    main()
