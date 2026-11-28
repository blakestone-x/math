"""Supplementary exact checks; the universal theorem is proved in Lean."""
from pathlib import Path
from math import comb
import hashlib
import json
import re
import sympy as sp

HERE = Path(__file__).resolve().parent
manifest = json.loads((HERE / "sources/manifest.json").read_text())
for item in manifest["sources"]:
    data = (HERE / "sources" / item["file"]).read_bytes()
    assert len(data) == item["bytes"]
    assert hashlib.sha256(data).hexdigest() == item["sha256"]
print("PASS: immutable source snapshot sizes and SHA256 hashes.")

def catalan(n):
    return comb(2*n, n)//(n+1)

limit = 200
b = [catalan(n//2) for n in range(limit+1)]
a = [sum(b[k]*b[n-k] for k in range(n+1)) for n in range(limit+1)]
printed = []
for line in (HERE/"sources/A104722.seq").read_text().splitlines():
    if re.match(r"%[STU] A104722 ", line):
        printed.extend(int(x) for x in line.split(" ",2)[2].split(",") if x.strip())
assert a[:len(printed)] == printed
print(f"PASS: all {len(printed)} source terms match the literal convolution.")
for r in range((limit-1)//2+1):
    assert a[2*r+1] == 2*catalan(r+1)
for r in range((limit-2)//2+1):
    assert a[2*r+2] == catalan(r+2)+catalan(r+1)
print("PASS: exact parity identities through n = 200.")

def residual(n):
    return ((n+4)*a[n]+(n+1)*a[n-1]-4*(n+1)*a[n-2]+4*(2-n)*a[n-3])

assert residual(3) == 4
assert all(residual(n) == 0 for n in range(4, limit+1))
print("PASS: residual at n = 3 is 4; every recurrence index 4 <= n <= 200 vanishes.")

r, c1, c2, c3 = sp.symbols("r c1 c2 c3")
h1 = (r+3)*c2-2*(2*r+3)*c1
h2 = (r+4)*c3-2*(2*r+5)*c2
even = (2*r+8)*(c3+c2)+(2*r+5)*(2*c2)-4*(2*r+5)*(c2+c1)+4*(2-(2*r+4))*(2*c1)
odd = (2*r+9)*(2*c3)+(2*r+6)*(c3+c2)-4*(2*r+6)*(2*c2)+4*(2-(2*r+5))*(c2+c1)
assert sp.expand(even-2*h2-6*h1) == 0
assert sp.expand(odd-6*h2-2*h1) == 0
print("PASS: both symbolic Catalan linear-combination certificates.")
print("PASS: supplementary verification complete; no finite test is used as the universal proof.")
