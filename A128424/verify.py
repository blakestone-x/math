"""Compare both defining rounding operations with the proposed linear tail."""
from math import isqrt


def verify():
    triangle = [1,3]
    pisot = [5,7]
    tail = [5,7,10]
    for _ in range(1500):
        x,y = triangle[-2:]
        triangle.append(isqrt(x*x+x*y+y*y))
        x,y = pisot[-2:]
        pisot.append((2*y*y+x)//(2*x))
        tail.append(tail[-1]+tail[-3]-1)
    assert triangle[3:] == tail[:len(triangle)-3] == pisot[:len(triangle)-3]
    assert 6000*83**50 < 100**50
    print(f'{len(triangle)-3} common terms from the three defining recurrences.')


if __name__ == '__main__':
    verify()
