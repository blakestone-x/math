"""Cross-check the general prefix intervals against direct scaled integer roots."""
from math import isqrt


def lower(W,k,h):
    return ((W*k+h)**2+W*W-1)//(W*W)


blocks = 0
for W in (2,3,4,5,7,8,9,10,16,25,27,100):
    for k in range(141):
        observed = [[] for i in range(W)]
        for n in range(k*k,(k+1)**2):
            observed[isqrt(W*W*n) % W].append(n)
        for h,values in enumerate(observed):
            high, low = lower(W,k,h+1), lower(W,k,h)
            assert list(range(low,high)) == values
            assert lower(W,k+W,h+1) - lower(W,k+W,h) == len(values)+2
            blocks += 1
print(f"{blocks} prefix blocks matched direct scaled integer square roots")

for h in range(10):
    starts = []
    for k in range(120):
        low = lower(10,k,h) + (h==0)
        high = lower(10,k,h+1)
        if h==1:
            assert high-low == (10*k+27)//50
        if low < high:
            starts.append(low)
    print(f"A{34106+h:06d}: {', '.join(map(str,starts[:8]))}")
    if h==2:
        a = [0]+starts
        assert a[:9] == [0,5,18,28,39,52,68,85,105]
        den = [1,-2,1,0,0,-1,2,-1]
        coeff = [sum(v*a[n-i] for i,v in enumerate(den) if i <= n) for n in range(len(a))]
        assert coeff[:9]==[0,5,8,-3,1,2,-2,-7,6] and all(v==0 for v in coeff[9:])

tri = [k*(k+1)//2 for k in range(100)]
seq = [n for n in range(10000) if 4*n < (2*isqrt(n)+1)**2]
assert all(seq[i] == k*k+(i-tri[k]) for k in range(99) for i in range(tri[k],tri[k+1]))
print('Wu recurrence and numerator verified; 4,950 triangular-index values matched')
