"""Independent, exact sign and root counts for the real-zero manuscript."""
from math import comb, factorial
from fractions import Fraction
from sympy import Poly, symbols, oo


def coefficients(n):
    return [comb(n,j)**2*comb(2*n-2*j,n) for j in range(n//2+1)]


def main():
    x=symbols('x')
    roots=0
    for n in range(2,49):
        a=coefficients(n)
        d=len(a)-1
        f=Poly.from_list(a[::-1],x)
        assert f.sqf_part().degree()==d and f.count_roots(-oo,0)==d
        # Derivative of the signed square-variable binomial row before reversal.
        for j in range(d+1):
            k=n-j
            assert a[j]*factorial(n) == comb(n,k)**2*factorial(2*k)//factorial(2*k-n)
        for j in range(d):
            num=(n-j)**2*(n-2*j)*(n-2*j-1)
            den=(j+1)**2*(2*n-2*j)*(2*n-2*j-1)
            assert a[j+1]*den==a[j]*num
        roots += d
    print(f'Exact squarefree and Sturm checks through n=48: {roots} negative roots.')
    for n in (64,128,256,512):
        a=coefficients(n); d=len(a)-1
        # At x=1 the predicted transform is 1/2. This output illustrates convergence.
        transform=Fraction(sum(j*v for j,v in enumerate(a)), d*sum(a))
        print(f'n={n}: transformed mean at x=1 is {float(transform):.9f}')


if __name__=='__main__':
    main()
