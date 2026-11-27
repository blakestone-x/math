"""Independent finite checks for digit-sum residues in rational bases. Python 3.10+."""
from collections import Counter
from fractions import Fraction
from math import gcd


def digits(n, p, q):
    """Least significant digit first, using the rational-base division algorithm."""
    out = []
    while n:
        n, d = divmod(q * n, p)
        out.append(d)
    return out


def predicted(p, q, m, step, offset, residue):
    g = gcd(m, step, p - q)
    return Fraction(g, m) if (residue - q * offset) % g == 0 else Fraction(0)


def digit_sums(limit, p, q):
    sums = [0] * limit
    for n in range(1, limit):
        parent, digit = divmod(q * n, p)
        sums[n] = sums[parent] + digit
    return sums


def check_representations():
    cases = 0
    for p in range(2, 13):
        for q in range(1, p):
            if gcd(q, p) != 1:
                continue
            sums = digit_sums(800, p, q)
            for n, s in enumerate(sums):
                assert (s - q*n) % (p-q) == 0
                if n < 80:
                    ds = digits(n, p, q)
                    assert sum(ds) == s
                    # Evaluate the digit string directly at the rational place values.
                    assert sum(d*Fraction(p, q)**j for j,d in enumerate(ds)) == q*n
                cases += 1
    return cases


def check_witnesses():
    cases = 0
    for p in range(2, 17):
        for q in range(1, p):
            if gcd(p, q) != 1:
                continue
            sums = digit_sums(3*p*p+100, p, q)
            for a in range(1, 65):
                if gcd(a, p) != 1:
                    continue
                v = q*a % p
                z = max(0, p-q-v) + v
                c = (pow(q, -1, p*p)*z-a) % (p*p)
                for n in range(c, 3*p*p, p*p):
                    assert sums[n+1]-sums[n] == q
                    assert sums[n+a+1]-sums[n+a] == 2*q-p
                    cases += 1
    return cases


def check_phase_counts():
    periods = 0
    strict_bounds = 0
    for p, q in ((2,1),(3,1),(3,2),(4,3),(5,2),(5,3),(7,2)):
        for k in range(2, 16):
            P, Q = p**k, q**k
            if P > 205_000:
                break
            # Lift low sums and ancestors independently one digit at a time.
            anc = list(range(P))
            low = [0] * P
            for _ in range(k):
                for i,n in enumerate(anc):
                    anc[i],digit = divmod(q*n,p)
                    low[i] += digit
            for a in (1,2,5,9):
                if gcd(a,p) != 1:
                    continue
                r = [(n+a) % P for n in range(P)]
                rise = [anc[r[n]] + Q*((n+a)//P) - anc[n] for n in range(P)]
                assert min(rise) >= 0 and sum(rise) == a*Q
                for h in (2,3,4,5):
                    if (p-q) % h == 0:
                        continue
                    marked = sum(v==0 and (low[n]-low[r[n]])%h!=0 for n,v in enumerate(rise))
                    assert P//(p*p) <= 2*(a*Q+marked)
                    if 4*a*Q*p*p <= P:
                        assert 4*p*p*marked >= P
                        strict_bounds += 1
                    periods += 1
    assert strict_bounds > 0
    return periods, strict_bounds


def check_distributions():
    profiles = ((3,2,7,1,0),(3,2,5,6,7),(5,2,6,6,1),(7,3,8,6,0),(7,3,8,6,1),(10,1,9,9,7))
    N = 120_000
    for p,q,m,a,b in profiles:
        sums = digit_sums(a*(N-1)+b+1,p,q)
        obs = Counter(sums[a*j+b] % m for j in range(N))
        model = [predicted(p,q,m,a,b,c) for c in range(m)]
        assert sum(model) == 1
        assert all(obs[c]==0 for c in range(m) if model[c]==0)
        print(f'{p}/{q}, m={m}, n={a}j+{b}: counts {[obs[c] for c in range(m)]}; predicted {list(map(str,model))}.')


if __name__ == '__main__':
    print(f'Digit-sum and congruence checks: {check_representations()}.')
    print(f'Two-digit carry witnesses: {check_witnesses()}.')
    total, positive = check_phase_counts()
    print(f'Exact phase-count inequalities: {total}, including {positive} tests at a depth satisfying the contraction threshold.')
    check_distributions()
