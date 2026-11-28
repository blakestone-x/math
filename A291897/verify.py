#!/usr/bin/env python3
"""Exact finite source checks; the unbounded proof is in EulerProof.lean."""
from fractions import Fraction
from math import comb
from pathlib import Path
import re
from sympy import Symbol, euler, expand

N = 200
numbers = []
for m in range(N + 1):
    numbers.append(0 if m % 2 else (1 if m == 0 else
        -sum(comb(m, j) * numbers[j] for j in range(m))))

def centered(m, x):
    return sum(comb(m, j) * numbers[m-j] * x**j for j in range(m+1))

def value(m, n):
    return Fraction(centered(m, 2*n-1), 2**m)

text = (Path(__file__).parent / 'sources/A291897.seq').read_text()
terms = []
for line in text.splitlines():
    if re.match(r'%[STU] A291897 ', line):
        terms.extend(map(int, line.split(' ', 2)[2].strip(',').split(',')))
assert [value(2*n-1, n).numerator for n in range(1, len(terms)+1)] == terms
print(f'PASS: all {len(terms)} frozen A291897 terms from the literal numerator definition')

x = Symbol('x')
for m in range(13):
    assert expand(centered(m, 2*x-1) - 2**m*euler(m, x)) == 0
print('PASS: centered definition equals independently computed Euler polynomials, degrees 0..12')

for n in range(1, 101):
    m = 2*n-1
    q = value(m, n)
    assert q.numerator % (m*m) == 0
print('PASS: conjecture replay for n=1..100 with exact reduced rational numerators')

for m in range(1, 26, 2):
    for k in range(-5, 6):
        q = Fraction(centered(m, k*m), 2**m)
        assert q.numerator % (m*m) == 0
print('PASS: generalized multiple-of-degree statement for odd m<=25 and -5<=k<=5')
print('Finite replay is supplementary; EulerNumerator.source_conjecture proves every positive n.')
