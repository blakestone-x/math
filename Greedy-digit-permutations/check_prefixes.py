"""Direct least-unused implementations checked against published OEIS prefixes.

Generate candidates from scratch at every step. The fixed-point certificate in
C++ uses independent per-digit cursors and only needs the eight induction seeds.
"""
from math import isqrt


def prime(n):
    return n >= 2 and all(n % d for d in range(2,isqrt(n)+1))


def extend(seq, rule, lower, length):
    used=set(seq)
    while len(seq)<length:
        y=lower
        while y in used or not rule(seq,y):
            y+=1
        seq.append(y)
        used.add(y)
    return seq


def root(x): return 1+(x-1)%9 if x else 0

def multiple(xs,y): return any(d!='0' and y%int(d)==0 for d in str(xs[-1]))

def share(xs,y): return y%2!=xs[-1]%2 and not set(str(xs[-1])).isdisjoint(str(y))

def request(xs,y): return str(root(xs[-1])) in str(y)

def bayonet(xs,y):
    d,f=xs[-1]%10,int(str(y)[0]); return y%10!=0 and (prime(10*d+f) or prime(10*f+d))

def join(xs,y):
    x=xs[-1]; ds=x%10+int(str(y)[0]); return ds!=0 and (x*10**len(str(y))+y)%ds==0

# Terms transcribed from fields S/T/U of the linked source entries.
EXPECTED = {
    'A218468': (
        1,2,4,8,16,3,6,12,5,10,7,14,9,18,11,13,15,
        17,19,20,22,24,26,28,30,21,23,27,32,33,36,39,42,34,
        40,44,48,52,25,35,45,50,55,60,54,56,65,66,72,38,51,
        29,46,64,68,78,49,63,57,70,77,84,76,90,81,31,37,69,
        96,99,108,41,43,75,80,88,104,47,91,53,85,95,100,58,105,
        59,110,61,62,
    ),
    'A318698': (
        0,101,10,1,12,11,14,13,16,15,18,17,70,7,72,21,2,
        23,20,25,22,27,24,29,26,61,6,63,30,3,32,31,34,33,
        36,35,38,37,74,41,4,43,40,45,42,47,44,49,46,65,50,
        5,52,51,54,53,56,55,58,57,76,67,60,69,62,121,28,81,
        8,
    ),
    'A318699': (
        1,10,11,12,13,14,15,16,17,18,19,90,9,92,21,2,23,
        20,25,22,27,24,29,26,61,6,63,30,3,32,31,34,33,36,
        35,38,37,70,7,72,47,4,41,40,43,42,45,44,49,46,65,
        50,5,52,51,54,53,56,55,58,57,74,67,60,69,62,121,28,
        81,8,83,48,85,68,87,76,71,78,73,130,39,94,59,96,79,
        98,89,80,101,0,103,100,91,102,105,104,107,106,109,108,
    ),
    'A340138': (
        0,10,1,11,2,12,3,13,4,14,5,15,6,16,7,17,8,
        18,9,19,21,23,25,27,29,20,22,24,26,28,31,34,37,41,
        35,38,32,45,39,30,33,36,49,40,42,46,51,56,52,47,62,
        48,43,57,53,58,44,68,50,54,59,55,61,67,64,71,78,60,
    ),
    'A350831': (
        1,3,2,9,5,31,4,7,6,11,12,32,33,8,34,13,14,
        15,35,36,16,17,18,37,19,21,38,39,22,91,41,42,92,93,
        23,24,71,43,25,94,72,95,96,73,26,74,75,97,44,76,77,
        45,98,99,27,46,78,301,47,48,302,303,28,304,79,29,
    ),
    'A275482': (
        1,2,4,5,10,11,12,15,18,20,8,19,25,14,22,17,28,
        9,24,36,40,13,16,38,39,27,30,3,6,60,26,37,56,34,
        48,75,42,35,21,32,46,53,41,45,29,54,78,52,44,31,23,
        67,43,47,74,88,33,66,55,50,64,79,65,76,7,70,62,51,
        84,100,68,80,71,58,99,90,72,59,94,105,82,101,102,96,103,
        92,95,49,81,69,87,104,
    ),
}
RULES = {'A218468':(1,multiple,1), 'A318698':(0,share,0), 'A318699':(1,share,0),
         'A340138':(0,request,1), 'A350831':(1,bayonet,1), 'A275482':(1,join,1)}
for key,(seed,rule,lower) in RULES.items():
    expected=EXPECTED[key]
    assert extend([seed],rule,lower,len(expected))==list(expected)
    print(f'{key}: all {len(expected)} source terms agree')
assert extend([0,10],lambda xs,y: str(root(xs[-2])) in str(y),1,3)==[0,10,20]
assert extend([1], join, 0, 2)==[1,0]
print('Both alternate conventions produced the stated initial terms')
