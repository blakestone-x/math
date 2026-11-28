from math import comb, isqrt
import numpy as np
from sympy import primerange
from itertools import accumulate
ps=[int(p) for p in primerange(5,202)]
N=2*ps[-1]-1
cats=[comb(2*j,j)//(j+1) for j in range(N+1)]
hs=[sum(comb(n,j)**2 * cats[j] for j in range(n+1)) for n in range(N+1)]
for p in ps:
 q=p*p
 M=np.array([[hs[i+j]%q for j in range(p)] for i in range(p)],dtype=np.int64)
 det=1
 for i in range(p-1):
  pivot=next(j for j in range(i,p) if M[j,i]%p)
  if pivot!=i:
   M[[i,pivot]]=M[[pivot,i]]
   det=-det
  a=int(M[i,i]);det=det*a%q
  col=(M[i+1:,i]*pow(a,-1,q))%q
  M[i+1:,i+1:]=(M[i+1:,i+1:] - np.outer(col,M[i,i+1:]))%q
 val=int(det*M[-1,-1])%q
 signed=(-1)**((p-1)//2)*val%q
 if p%6==5:
  k=(p+1)//6
  predict=(-3*p*pow(comb(3*k,k),-1,q))%q
 else:
  x=next(x for x in range(-isqrt(p),isqrt(p)+1) if x%3==1 and (p-x*x)%3==0 and isqrt((p-x*x)//3)**2==(p-x*x)//3)
  predict=(2*x-p*pow(2*x,-1,q))%q
 assert signed==predict,(p,signed,predict)
print("Raw Catalan moment determinants by modular elimination match both full conjectural branches for all",len(ps),"primes 5 through",ps[-1])
