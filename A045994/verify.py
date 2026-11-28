"""Supplementary exact checks; the universal proof is in Lean."""
from pathlib import Path
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

limit = 200
m = [1, 1]
for n in range(limit - 1):
    m.append(m[n + 1] + sum(m[k] * m[n - k] for k in range(n + 1)))
a = [1]
for n in range(1, limit + 1):
    a.append(m[n] + sum(m[k] * a[n - k - 1] for k in range(1, n)))
text = (HERE / "sources/A045994.seq").read_text()
printed = []
for line in text.splitlines():
    if re.match(r"%[STU] A045994 ", line):
        printed.extend(int(x) for x in line.split(" ", 2)[2].split(",") if x.strip())
assert a[:len(printed)] == printed
print(f"PASS: all {len(printed)} source terms match the literal recurrence.")

for n in range(5, limit + 1):
    assert ((n + 1)*a[n] + 2*(-2*n - 1)*a[n - 1]
            + 2*(-n + 3)*a[n - 2] + (11*n - 19)*a[n - 3]
            + (11*n - 27)*a[n - 4] + 3*(n - 3)*a[n - 5]) == 0
print(f"PASS: exact recurrence checks for every 5 <= n <= {limit}.")

x, A, M, dA = sp.symbols("x A M dA")
p = x**4 + 3*x**3 + 2*x**2 - x
q = x**2 + 2*x - 1
U, V = 1 + x*A, (1 + x)*A
certificate = (U**2*(x**2*M**2 + (x-1)*M + 1)
               - (U*M-V)*(x**2*(U*M+V)+(x-1)*U))
assert sp.expand(certificate-(p*A**2+q*A+1)) == 0
u = x - 4*x**2 - 2*x**3 + 11*x**4 + 11*x**5 + 3*x**6
v = 1 - 6*x + 2*x**2 + 14*x**3 + 17*x**4 + 6*x**5
w = 1 - 4*x + x**2
L = 1 - 6*x + 8*x**2 + 2*x**3 - x**4
certificate = ((2*p*A+q)*(u*dA+v*A-w)
               - u*((2*p*A+q)*dA+sp.diff(p,x)*A**2+sp.diff(q,x)*A)
               - L*(p*A**2+q*A+1))
assert sp.expand(certificate) == 0
print("PASS: exact polynomial elimination and differential certificates.")

wrong = sp.series(1/(1-x*(1+x)*sum(m[k]*x**k for k in range(4))),x,0,4)
assert wrong.removeO().coeff(x, 3) == 8 and a[3] == 7
print("PASS: printed generating function has coefficient 8 at x^3; source has 7.")
print("PASS: supplementary verification complete; no finite test is used as the universal proof.")
