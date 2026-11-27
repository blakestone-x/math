"""Build both triangles directly and compare with the bit formulas."""
from math import comb


def verify():
    last = 256
    rows = [[0]]
    reflected = [[0]]
    for n in range(1,last+1):
        past = rows[-1]
        rows.append([0]+[past[k-1]^past[k] for k in range(1,n)]+[n])
        previous = reflected[-1]+[0]
        reflected.append([0,n]+[previous[k-1]^previous[k] for k in range(2,n+1)])
        assert rows[n][1:] == reflected[n][1:][::-1]
        if n <= 64:
            for k in range(1,n+1):
                value = 0
                for j in range(k.bit_length()):
                    bit = sum(comb(n-s,k-s) for s in range(2**j,k+1,2**j)) % 2
                    value += bit << j
                assert value == rows[n][k]
        if n & (n-1) == 0:
            assert rows[n] == [k if k>0 and k&(k-1)==0 else 0 for k in range(n+1)]
    for k in range(1,65):
        for j in range(k.bit_length()):
            e = k-2**j+1
            period = 1<<(e-1).bit_length()
            bits = [(rows[n][k]>>j)&1 for n in range(k,last+1)]
            assert bits[:-period] == bits[period:]
            if period > 1:
                half = period//2
                assert bits[:half] != bits[half:period]
    print('256 rows by both XOR recurrences, all binomial entries through row 64, '
          'and the bit periods of the first 64 columns agree.')


if __name__ == '__main__':
    verify()
