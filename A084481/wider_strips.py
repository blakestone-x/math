"""Exact certificates for the conjectured recurrences in OEIS A183305 and A183306."""
from itertools import product

# Coefficients multiply a(n-1), a(n-2), ... respectively.
RECURRENCE = {
    4: [5,-6,1,1,-9,4,1,28,-16,-3,2,-6,2,-1],
    5: [9,-26,24,47,-157,-43,641,-643,-952,3460,-2021,-2111,2715,-1249,-4657,
        -1514,1961,-1230,6713,8832,10212,1971,-6552,-2819,-2898,-973,302,433,286],
}
START = {4: 16, 5: 32}

def valid(width, a, b, c):
    for j in range(width):
        v = b >> j & 1
        horizontal = [(b >> k) & 1 for k in (j-1,j+1) if 0 <= k < width]
        vertical = [r >> j & 1 for r in (a,c) if r is not None]
        neighbors = horizontal + vertical
        if 2*neighbors.count(v) > len(neighbors):
            return False
    return True

def prove(width, coefs, start):
    rows = range(2**width)
    pairs = list(product(rows,repeat=2))
    ix = {p:i for i,p in enumerate(pairs)}
    # Restrict top-left bit to zero to pick a single representative of each complement pair.
    S = [int(a%2 == 0 and valid(width,None,a,b)) for a,b in pairs]
    E = [int(valid(width,a,b,None)) for a,b in pairs]
    edges = [[ix[b,c] for c in rows if valid(width,a,b,c)] for a,b in pairs]

    def closure(starts,edges):
        seen = set(starts); todo = list(seen)
        while todo:
            i = todo.pop()
            for j in edges[i]:
                if j not in seen:
                    todo.append(j)
                    seen.add(j)
        return seen

    rev = [[] for _ in pairs]
    for i,js in enumerate(edges):
        for j in js:
            rev[j].append(i)
    good = sorted(closure((i for i,v in enumerate(S) if v), edges)
                  & closure((i for i,v in enumerate(E) if v), rev))
    ix = {i:j for j,i in enumerate(good)}
    E = [E[i] for i in good]
    V = [S[i] for i in good]
    edges = [[ix[j] for j in edges[i] if j in ix] for i in good]

    def step(V):
        W = [0]*len(V)
        for i,js in enumerate(edges):
            for j in js:
                W[j] += V[i]
        return W

    # Check d consecutive recurrence residuals. Each residual at n>=start
    # is a fixed linear combination of entries of M^(n-start), hence itself
    # satisfies the monic characteristic recurrence of degree d.
    first = sum(valid(width,None,b,None) for b in rows if b%2 == 0)
    terms = [0,first]
    d = len(good)
    for n in range(2,start+d):
        terms.append(sum(w*e for w,e in zip(V,E)))
        V = step(V)
    for n in range(start,start+d):
        assert terms[n] == sum(c*terms[n-j] for j,c in enumerate(coefs,1))
    print(f"Width {width}: {d} productive states, residual zero for {start} <= n <= {start+d-1}.")
    Q = [1]+[-c for c in coefs]
    P = [sum(Q[j]*terms[i-j] for j in range(min(len(Q)-1,i)+1)) for i in range(start)]
    print(f"Numerator (low degree first): {P}")
    if width == 4:
        N = [-6,11,4,-11,13,14,-56,-15,46,-19,13,1,0,1]
        empirical = [(2*Q[i-1] if 1<=i<=len(Q) else 0)
                     -(N[i-2] if 2<=i<=len(N)+1 else 0) for i in range(start)]
        assert P == empirical
    return P

if __name__ == "__main__":
    for width,coefs in RECURRENCE.items():
        prove(width,coefs,START[width])
