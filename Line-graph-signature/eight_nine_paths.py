"""Independent arithmetic check of the weak single-edge signature bound."""
from fractions import Fraction as F
from itertools import product
from collections import Counter


def check(path, counts):
    # -2,+2 denote signed equalities; -1,+1 denote odd signed edges.
    s = len(path)
    groups, signs = [0], [1]
    for edge in path:
        if abs(edge) == 2:
            groups.append(groups[-1]); signs.append(signs[-1] * (edge // 2))
        else:
            groups.append(1 + groups[-1]); signs.append(1)
    n = 1 + groups[-1]
    size = [0] * n
    for i in range(1, s):
        size[groups[i]] += 1
    if n == 1:
        assert size[0] == s - 1
        for left, right in [(1,1),(1,-1),(0,0),(1,0),(0,1)]:
            if right == signs[-1] * left:
                assert sum(2*(left*signs[i])**2 for i in range(1,s)) == 2*size[0]*left**2
        counts["all-even"] += 1
        return
    # Build the restricted matrix on the component variables, expressed using
    # the actual endpoint variables at both boundaries.
    tail = signs[-1]
    for i in range(s+1):
        if groups[i] == n-1:signs[i] *= tail
    mat = [[F(0)] * n for _ in range(n)]
    for i in range(1,s):
        u=groups[i];mat[u][u] += 2
    for i,edge in enumerate(path):
        if abs(edge)==1:
            u,v=groups[i:i+2];sg=edge*signs[i]*signs[i+1]
            mat[u][v]+=sg;mat[v][u]+=sg
    # Eliminate internal coordinates directly by exact Schur complements.
    for k in range(1,n-1):
        pivot=mat[k][k];assert pivot>0
        active=[0]+list(range(k+1,n))
        for i in active:
            for j in active:
                mat[i][j] -= mat[i][k]*mat[k][j]/pivot
    d0,d1=2*size[0]-mat[0][0],2*size[-1]-mat[-1][-1]
    remaining_loss=sum(size[1:-1])-(n-2)
    assert remaining_loss+(size[0]+size[-1])==(s-1)-(n-2)
    target=[0] if remaining_loss else [1,-1]
    found=False
    for sign in target:
        d01=sign-mat[0][-1]
        if d0>=0 and d1>=0 and d0*d1>=d01*d01:
            for x,y in [(1,1),(1,-1),(0,1),(1,0),(0,0)]:
                assert d0*x*x+2*d01*x*y+d1*y*y>=0
            found=True;break
    assert found,(path, size, mat)
    counts["cut" if remaining_loss else "odd"]+=1


counts=Counter()
for segments in range(1,9):
    for p in product((-2,-1,1,2), repeat=segments):check(p,counts)
print(dict(counts), "path decorations", sum(counts.values()))
