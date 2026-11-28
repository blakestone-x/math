"""Exact transfer enumerations for OEIS A183304 and A084481."""
from collections import Counter, deque
from itertools import product
import sympy as sp

x = sp.symbols("x")

def valid(above, row, below):
    def bit(i, r):
        return r >> i & 1
    for i in range(3):
        neighbors = [bit(j, row) for j in (i-1, i+1) if 0 <= j < 3]
        neighbors += [bit(i, r) for r in (above, below) if r is not None]
        if 2 * neighbors.count(bit(i, row)) > len(neighbors):
            return False
    return True

def orientations():
    base = ((0,0),(0,1),(0,2),(1,2))
    shapes = set()
    for fx, fy, swap in product((-1,1),(-1,1),(False,True)):
        raw = [(fx*(b if swap else a), fy*(a if swap else b)) for a,b in base]
        x0,y0 = map(min,zip(*raw))
        shapes.add(tuple(sorted((a-x0,b-y0) for a,b in raw)))
    return sorted(shapes)

def tiling_matrix():
    tiles = orientations()
    def advance(mask):
        out = Counter()
        def fill(mask):
            free = next((r for r in range(4) if not(mask >> r & 1)), None)
            if free is None:
                out[mask >> 4] += 1
                return
            for tile in tiles:
                # Anchor each possible tile at the first free cell of column 0.
                anchor = min(b for a,b in tile if a==0)
                cells = [(a, b+free-anchor) for a,b in tile]
                if any(b<0 or b>=4 for _,b in cells):
                    continue
                bits = sum(1 << (4*a+b) for a,b in cells)
                if mask & bits == 0:
                    fill(mask | bits)
        fill(mask)
        return out
    todo, trans = deque([0]), {}
    while todo:
        state = todo.popleft()
        if state in trans:
            continue
        trans[state] = advance(state)
        todo.extend(trans[state])
    states = sorted(trans)
    M = sp.Matrix([[trans[i][j] for j in states] for i in states])
    return M, states

def reduced_matrix(states, M, S, E, canonical):
    """Keep states on feasible paths and merge by the stated symmetry."""
    reachable = {i for i in range(len(states)) if S[i]}
    finishable = {i for i in range(len(states)) if E[i]}
    for _ in states:
        reachable |= {j for i in reachable for j in range(len(states)) if M[i,j]}
        finishable |= {i for j in finishable for i in range(len(states)) if M[i,j]}
    selected = sorted(reachable & finishable)
    reps = sorted({canonical(states[i]) for i in selected})
    members = [[i for i in selected if canonical(states[i]) == r] for r in reps]
    R = sp.Matrix([[sum(M[states.index(r),j] for j in group)
                    for group in members] for r in reps])
    for i in selected:
        row = [sum(M[i,j] for j in group) for group in members]
        assert row == list(R.row(reps.index(canonical(states[i]))))
    U = sp.Matrix([[sum(S[i] for i in group) for group in members]])
    V = sp.Matrix([E[states.index(r)] for r in reps])
    return reps, R, U, V

def binary_matrix():
    pairs = list(product(range(8), repeat=2))
    M = sp.zeros(len(pairs))
    for i,(u,v) in enumerate(pairs):
        for w in range(8):
            if valid(u,v,w):
                M[i,pairs.index((v,w))] = 1
    S = sp.Matrix([int(valid(None, u,v)) for u,v in pairs])
    E = sp.Matrix([int(valid(u,v,None)) for u,v in pairs])
    def canonical(pair):
        u,v = pair
        rev = lambda r: int(f"{r:03b}"[::-1], 2)
        return min((a^k,b^k) for a,b in ((u,v),(rev(u),rev(v))) for k in (0,7))
    return reduced_matrix(pairs, M, S, E, canonical)

def tiling_reduced_matrix():
    M, states = tiling_matrix()
    e = sp.Matrix([int(i == 0) for i in states])
    def canonical(i):
        rev = lambda r: int(f"{r:04b}"[::-1],2)
        return min(i, rev(i%16) + 16*rev(i//16))
    return reduced_matrix(states, M**2, e, e, canonical)

if __name__ == "__main__":
    reps, R, U, V = binary_matrix()
    print("Array states:", reps, "matrix:", R, "start:", U/2, "end:", V.T, sep="\n")
    b1 = sum(valid(None, r, None) for r in (0,2,4,6))
    B = sp.factor(b1*x + x**2*(U*(sp.eye(R.rows)-x*R).inv()*V)[0]/2)
    assert sp.cancel(B-x*(1+x)**2/(1-2*x-x**3)) == 0
    print("Array series:", B)
    states, P, u, v = tiling_reduced_matrix()
    print("Tiling states:", states, "matrix:", P, sep="\n")
    T = sp.factor((u*(sp.eye(P.rows)-x*P).inv()*v)[0])
    L = sp.factor(1-1/T)
    print("Indecomposable tiling series:", L)
    assert sp.cancel(L-2*x*B-2*x*(1+x)**2) == 0
    print("Verified exact rational generating-function identity.")
