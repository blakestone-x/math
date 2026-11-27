"""Construct the circular order and independently check every unit and edge label."""
from math import gcd


def prime_powers(n):
    result = []
    divisor = 2
    while divisor * divisor <= n:
        if n % divisor == 0:
            power = 1
            while n % divisor == 0:
                n //= divisor
                power *= divisor
            result.append((divisor, power))
        divisor += 1
    if n > 1:
        result.append((n, n))
    return result


def primitive(p, power):
    period = (power//p)*(p-1)
    divisors = [prime for prime, _ in prime_powers(period)]
    for g in range(2, power):
        if gcd(g,power)==1 and all(pow(g, period//r, power)!=1 for r in divisors):
            return g
    raise AssertionError(f'Primitive root missing at {power}')


def construct(n):
    factors = prime_powers(n)
    p, modulus = factors[0]
    root = primitive(p, modulus)
    period = (modulus//p)*(p-1)
    low = [pow(root,i,modulus) for i in range(period)]
    for p, high_mod in factors[1:]:
        g = primitive(p, high_mod)
        d = (high_mod//p)*(p-1)
        inverse = pow(g,-1,high_mod)
        multipliers = [pow(g,2,high_mod),inverse] + [g,inverse]*((len(low)-2)//2)
        inv_modulus = pow(modulus,-1,high_mod)
        result = []
        y = 1
        for _ in range(d):
            for x, multiplier in zip(low,multipliers):
                # Solve v=x mod modulus and v=y mod high_mod.
                result.append(x + modulus*((y-x)*inv_modulus % high_mod))
                y = y*multiplier % high_mod
        assert y==1
        low, modulus = result, modulus*high_mod
    return low


def check(n):
    units = {x for x in range(n) if gcd(x,n)==1}
    order = construct(n)
    edges = tuple(zip(order,order[1:]+order[:1]))
    assert len(order)==len(units) and set(order)==units
    assert {(x-y)%n for x,y in edges}==units
    if n%3:
        assert {(x+y)%n for x,y in edges}==units
    return len(units)


if __name__=='__main__':
    if not __debug__:
        raise SystemExit('Use Python with assertions enabled.')
    cases = list(range(3,1502,2)) + [3**3*5**2*7, 5**2*7**2*11, 3*5*7*11*13]
    edges = sum(map(check,cases))
    print(f'Checked {len(cases)} odd moduli and {edges:,} directed edges.')
    print('n=15 circular order:',construct(15))
    print('n=35 circular order:',construct(35))
    print('n=35 sums and differences both exhaust the 24 units.')
