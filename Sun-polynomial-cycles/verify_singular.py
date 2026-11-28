"""Build one cyclic labeling for every singular matrix in the indicated spaces."""
from itertools import permutations, product
from math import factorial


class Space:
    def __init__(self, p, d):
        self.p, self.d, self.q = p, d, p**d
        self.units = [p**i for i in range(d)]
        ds = [[(x//u) % p for u in self.units] for x in range(self.q)]
        self.add = [[sum(((a+b) % p)*u for a,b,u in zip(ax,ay,self.units))
                     for ay in ds] for ax in ds]
        self.scale = [[sum((a*t % p)*u for a,u in zip(ax,self.units)) for ax in ds]
                      for t in range(p)]
        self.ds = ds

    def extend(self, values, v):
        return {self.add[x][self.scale[t][v]] for t in range(self.p) for x in values}

    def matrix(self, cols):
        vals = [0]
        for v in cols:
            vals = [self.add[x][self.scale[t][v]] for t in range(self.p) for x in vals]
        return vals

    def count_all(self, L):
        q, add = self.q, self.add
        count = 0
        for tail in permutations(range(1,q)):
            circ = (0,)+tail
            if len({add[L[x]][circ[(i+1)%q]] for i,x in enumerate(circ)}) == q:
                count += 1
        return count

    def construct(self, L):
        q,p,d,add=self.q,self.p,self.d,self.add
        K=[x for x in range(q) if L[x]==0]
        k=len(K)
        if k==q:
            return list(range(1,q))+[0]
        h=K[1]
        if p==2 and d==2:
            for a,b,c in permutations((1,2,3)):
                order=(0,a,b,c)
                S=[0]*4
                for i,x in enumerate(order): S[x]=order[(i+1)%4]
                if len({add[L[x]][S[x]] for x in range(q)})==q: return S
            raise AssertionError("missing small circuit")
        basis=[h]
        span={0,h} if p==2 else self.extend({0},h)
        image={0}
        directions={0}
        cap=set(range(q))
        if p==2:
            for mask in range(1,q):
                H={x for x in range(q) if (mask & x).bit_count()%2==0}
                if h in H: continue
                choices=[x for x in H if L[x] not in H]
                if choices: break
            else: raise AssertionError("no hyperplane")
            cap=H
            e=min(choices)
            basis.append(e)
            span=self.extend(span,e); image=self.extend(image,e); directions=self.extend(directions,e)
        while len(basis)<d:
            last=basis[-1]
            e=next(x for x in sorted(cap) if x not in span and add[x][L[last]] not in directions)
            basis.append(e); span=self.extend(span,e); image=self.extend(image,e)
            directions=self.extend(directions,add[e][L[last]])
        end=next(x for x in range(q) if x not in image and add[x][L[basis[-1]]] not in directions)
        domain=self.matrix(basis)
        outputs=self.matrix(basis[1:]+[end])
        S=[0]*q
        for x,y in zip(domain,outputs): S[x]=y
        assert len(set(S))==q and len({add[L[x]][S[x]] for x in range(q)})==q
        # Merge cycles with transpositions in a common kernel coset.
        roots=list(range(q))
        def root(x):
            while roots[x]!=x:
                roots[x]=roots[roots[x]]; x=roots[x]
            return x
        for x,y in enumerate(S):
            roots[root(x)]=root(y)
        for x in range(q):
            y=add[x][h]
            rx,ry=root(x),root(y)
            if rx!=ry:
                S[x],S[y]=S[y],S[x]
                roots[rx]=ry
        return S


def run(p,d,all_circles=False,sample=None):
    V=Space(p,d); q=V.q; mats=cycles=0
    if sample is None:
        columns=product(range(q),repeat=d)
    else:
        from random import Random
        rng=Random(245211+q)
        columns=([rng.randrange(q) for _ in range(d-1)]+[0] for _ in range(sample))
    for cols in columns:
        L=V.matrix(cols)
        k=L.count(0)
        if k==1: continue
        S=V.construct(L); visited=set(); x=0
        while x not in visited:
            visited.add(x);x=S[x]
        assert x==0 and len(visited)==q and len({V.add[L[j]][S[j]] for j in range(q)})==q
        mats+=1
        if all_circles:
            actual=V.count_all(L)
            assert actual>=factorial(k)**(q//k)//k
            cycles+=actual
    print(f"F_{p}^{d}: {mats} singular maps checked" + (f", {cycles} valid circles in full enumeration" if all_circles else ""))


if __name__=="__main__":
    for p,d in [(2,2),(2,3),(3,2)]:
        run(p,d,all_circles=True)
    run(2,4)
    for p,d in [(2,5),(2,6),(3,3),(5,2),(7,2)]:
        run(p,d,sample=20)
