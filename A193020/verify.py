"""Exact output sets, periodic factors, and small ordered-tree profiles."""
from functools import cache
from itertools import groupby, permutations, product
from math import comb, prod


def shuffle_count(word):
    n = len(word)

    @cache
    def outputs(i, j):
        if i == n:
            return {word[j:]}
        if j == n:
            return {word[i:]}
        return ({word[i] + v for v in outputs(i+1, j)} |
                {word[j] + v for v in outputs(i, j+1)})

    return len(outputs(0, 0))


def periodic_factors(alphabet, n):
    factors = {a*n for a in alphabet}
    for a,b in permutations(alphabet, 2):
        for u,v in product(range(1,n+1), repeat=2):
            period = a*u + b*v
            extended = period*(2+n//len(period))
            factors.update(extended[i:i+n] for i in range(len(period)))
    return factors


def profiles(n):
    if n == 0:
        yield ()
    for r in range(1,n+1):
        for rest in profiles(n-r):
            yield (r,)+rest


def check_rotating_copies():
    for copies in range(2,10):
        for letters in range(2,copies+1):
            cycles = 4
            # Mark the first 'letters' slots clockwise, leaving the others empty.
            advanced = [s if s<letters else 0 for s in range(copies)]
            starting = advanced[:]
            for tick in range(copies*(cycles-1)):
                for mark in range(letters):
                    copy = (mark-tick)%copies
                    assert advanced[copy] < letters*cycles
                    assert advanced[copy]%letters == mark
                    advanced[copy] += 1
            assert all(a-b==letters*(cycles-1) for a,b in zip(advanced,starting))


def verify():
    expected = [1,2,4,9,18,54,120,324]
    roots = 0
    for alphabet, limit in [('01',8),('012',6)]:
        for n in range(1,limit+1):
            factors = periodic_factors(alphabet,n)
            maximum = 0
            for letters in product(alphabet, repeat=n):
                w = ''.join(letters)
                runs = [sum(1 for _ in group) for _,group in groupby(w)]
                bound = prod(comb(a+b,a) for a,b in zip(runs,runs[1:]))
                actual = shuffle_count(w)
                assert actual >= bound
                assert (actual == bound) == (w in factors)
                if len(runs) > 1:
                    assert (actual == n) == (len(runs)==2 and min(runs)==1)
                maximum = max(maximum,actual)
                roots += 1
            if len(alphabet) == 2:
                assert maximum == expected[n-1]
    for k in range(4,13):
        values = [3*(k-2),k*(k-1)//2,2*(k-1),k,1,k+1,k*k,
                  2*(k-1)**2,k*(k-1)**2//2]
        for j,value in zip(range(-5,4),values):
            assert shuffle_count(format(2**k+j,'b')) == value
    for n in range(1,12):
        by_height = [0]*(n+1)
        for levels in profiles(n):
            by_height[len(levels)] += prod(comb(a+b-1,b) for a,b in zip(levels,levels[1:]))
        for h in range(1,n+1):
            ways = [1]+[0]*h
            for _ in range(2*n):
                ways = [sum(ways[j] for j in (i-1,i+1) if 0<=j<=h) for i in range(h+1)]
            assert sum(by_height[:h+1]) == ways[0]
    check_rotating_copies()
    print(f'{roots} binary and ternary roots; binary maxima through length 8; '
          'all nine offsets for k=4..12; all height bounds through 11 edges.')


if __name__ == '__main__':
    verify()
