"""Counts two-column balanced arrays by assigning the entries of each letter."""
from csv import reader
from math import comb
from pathlib import Path


def arrays(q, n):
    u, high = divmod(2*n, q)
    states = {(0, 0): 1}  # (number of high multiplicities, left-column length)
    for i in range(1, q+1):
        new = {}
        for (k, left), count in states.items():
            for bit in (0, 1):
                h = k + bit
                if h > high or h + q-i < high:
                    continue
                minimum = max(left, (i*u+h+1)//2)
                maximum = min(n, left+u+bit)
                for end in range(minimum, maximum+1):
                    key = h, end
                    new[key] = new.get(key, 0) + count
        states = new
    return states[high, n]


def bridges(j, k, m, e):
    if (j*e+k) % 2:
        return 0
    total = 0
    for a in range(j-k+1):
        for b in range(k+1):
            h = a+b
            if 2*h >= j:
                continue
            top = (j-2*h)*m + (j*e+k)//2 - a*(e+1) - b*(e+2) + j-1
            total += (-1)**h * comb(j-k, a)*comb(k, b)*comb(top, j-1)
    return comb(j, k)*total


def excursions(q, n):
    m, s = divmod(n, q)
    e, t = divmod(2*s, q)
    bridge = {(j,k): bridges(j,k,m,e) for j in range(1,q+1)
              for k in range(min(j,t)+1)}
    result = {(0,0): 1}
    for j in range(1, q+1):
        for k in range(min(j,t)+1):
            total = sum(count*result.get((j-i,k-l), 0)
                        for (i,l),count in bridge.items() if i <= j and l <= k)
            quotient, remainder = divmod(total, j)
            assert remainder == 0
            result[j,k] = quotient
    return result[q,t]


def differences(values):
    result = []
    while values:
        result.append(values[0])
        values = [b-a for a,b in zip(values, values[1:])]
    return result


def divide_monic(poly, divisor):
    result = poly[:]
    quotient = [0]*max(0,len(poly)-len(divisor)+1)
    for i in range(len(quotient)-1,-1,-1):
        quotient[i] = result[i+len(divisor)-1]
        for j,c in enumerate(divisor):
            result[i+j] -= quotient[i]*c
    return quotient if not any(result) else None


def check_denominator(q, formulas):
    # Numerator at common denominator (1-x^q)^q, in ascending powers.
    numerator = [0]*(q*q)
    for s in range(q):
        for i,d in enumerate(formulas[q,s]):
            for j in range(q-i):
                numerator[s+q*(i+j)] += d*(-1)**j*comb(q-1-i,j)
    factors = {1:[-1,1],2:[1,1],3:[1,1,1],4:[1,0,1],
               5:[1]*5,6:[1,-1,1],7:[1]*7,8:[1,0,0,0,1]}
    for order,phi in factors.items():
        if q%order:
            continue
        reduced = numerator[:]
        while reduced and reduced[-1]==0:
            reduced.pop()
        exponent = q
        while exponent and (quotient := divide_monic(reduced,phi)) is not None:
            reduced = quotient
            exponent -= 1
        expected = q if q%2 or (q//2)%order==0 else q-1
        assert exponent==expected,(q,order,exponent)


def verify():
    rows = list(reader(Path(__file__).with_name('coefficients.csv').read_text().splitlines()))
    assert rows[0][:3] == ['q','s','d0']
    formulas = {(int(q),int(s)): [int(x) for x in ds if x] for q,s,*ds in rows[1:]}
    assert set(formulas) == {(q,s) for q in range(3,9) for s in range(q)}
    count = 0
    for (q,s), coefficients in formulas.items():
        values = []
        for m in range(q+3):
            n = q*m+s
            direct = arrays(q,n)
            assert direct == excursions(q,n)
            assert direct == sum(d*comb(m,i) for i,d in enumerate(coefficients))
            values.append(direct)
            count += 1
        assert differences(values[:q]) == coefficients
    for q in (2,9,10):
        for n in range(2*q+1):
            assert arrays(q,n) == excursions(q,n)
    for q in range(3,9):
        check_denominator(q,formulas)
    print(f'33 constituent polynomials verified in {count} direct comparisons; '
          'the bridge formula also agrees for alphabets 2, 9 and 10.')


if __name__ == '__main__':
    verify()
