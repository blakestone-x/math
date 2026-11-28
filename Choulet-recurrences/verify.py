"""Verify the printed OEIS recurrences by exact coefficient comparison.

Usage: python verify.py [--source-dir /path/to/seq/files]
Needs SymPy. The CSV is a normalized transcription of the 80 primary-source
recurrences. --source-dir also compares it with the pinned OEIS .seq files.
"""
import argparse
import ast
import csv
import hashlib
import re
from pathlib import Path

import sympy as sp

HERE = Path(__file__).resolve().parent
REVISION = "091a90f51479669655f4e46343867ea2abd5d4ff"
X, N = sp.symbols("x n")
TERMS = sp.symbols("a0:6")


def operator(b, k, ell):
    s = 1 if k == 0 else 2
    den = (1 - X) ** s
    forcing = 1 + (b - 1) * X + ell * X**2 / (1 - X) + k * X**2 * (2 - X) / (1 - X)**2
    S = sp.Poly(sp.cancel(den * (1 - 4 * X * forcing)), X)
    B = sp.Poly((1 - X) * S.as_expr(), X)
    E = sp.Poly((1 - X) * S.diff().as_expr() + s * S.as_expr(), X)
    return [sp.expand((N + 1 - j) * B.nth(j) - (E.nth(j - 1) / 2 if j else 0))
            for j in range(6)], E


def arithmetic(node, variables):
    """Read integer polynomial expressions without executing source text."""
    if isinstance(node, ast.Constant) and type(node.value) is int:
        return sp.Integer(node.value)
    if isinstance(node, ast.Name) and node.id in variables:
        return variables[node.id]
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.UAdd, ast.USub)):
        value = arithmetic(node.operand, variables)
        return -value if isinstance(node.op, ast.USub) else value
    if isinstance(node, ast.BinOp):
        left, right = arithmetic(node.left, variables), arithmetic(node.right, variables)
        if isinstance(node.op, ast.Add):
            return left + right
        if isinstance(node.op, ast.Sub):
            return left - right
        if isinstance(node.op, ast.Mult):
            return left * right
        if isinstance(node.op, ast.Pow) and right in (0, 1, 2, 3):
            return left**right
    raise ValueError(ast.dump(node))


def read_source(path):
    raw = path.read_bytes()
    title = next(line for line in raw.decode().splitlines() if line.startswith("%N "))
    b, k, ell = map(int, re.search(
        r"a\(1\)\s*=\s*(-?\d+).*?\bk\s*=\s*(-?\d+)\s+and\s+l\s*=\s*(-?\d+)", title, re.I
    ).groups())
    assert re.search(r"a\(0\)\s*=\s*1\b", title) and "a(p)*a(n-p)+k" in title.replace(" ", "").lower()
    assert "n>=1" in title.replace(" ", "").lower()
    formulas = re.findall(r"^%[CF] A\d+ Conjecture:\s*(.*?=\s*0)\.", raw.decode(), re.M | re.I)
    assert len(formulas) == 1, path
    lhs = formulas[0].split("=")[0].replace(" ", "").replace("^", "**")
    lhs = re.sub(r"a\(n(?:-(\d+))?\)", lambda m: "A_" + (m[1] or "0"), lhs)
    lhs = re.sub(r"(?<=[0-9)])(?=[(nA])|(?<=n)(?=\()", "*", lhs)
    variables = {"n": N, **{f"A_{i}": a for i, a in enumerate(TERMS)}}
    expr = sp.expand(arithmetic(ast.parse(lhs, mode="eval").body, variables))
    coeffs = [expr.coeff(a) for a in TERMS]
    assert expr == sp.expand(sum(c * a for c, a in zip(coeffs, TERMS)))
    data = ",".join(line.split(" ", 2)[2].strip(",") for line in raw.decode().splitlines()
                    if line.startswith(("%S ", "%T ", "%U ")))
    return (path.stem, b, k, ell, *[str(c) for c in coeffs], hashlib.sha256(raw).hexdigest()), list(map(int, data.split(",")))


def terms(b, k, ell, count):
    seq = [1, b]
    while len(seq) < count:
        n = len(seq) - 1
        seq.append(sum(seq[i] * seq[n - i] for i in range(n + 1)) + (n + 1)*k + ell)
    return seq


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-dir", type=Path)
    args = parser.parse_args()
    audited = 0
    boundaries = 0
    with (HERE / "identities.csv").open(newline="") as f:
        for row in csv.DictReader(f):
            ident = row["sequence"]
            b, k, ell = map(int, (row["b"], row["k"], row["ell"]))
            expected, E = operator(b, k, ell)
            given = [arithmetic(ast.parse(row[f"shift_{j}"], mode="eval").body, {"n": N}) for j in range(6)]
            multiplier = sp.cancel(given[0] / (N + 1))
            assert multiplier in (1, N), (ident, multiplier)
            assert all(sp.expand(c - multiplier*d) == 0 for c, d in zip(given, expected)), ident
            lag = max(j for j, c in enumerate(given) if c != 0)
            seq = terms(b, k, ell, 40)
            for n in range(lag, 40):
                assert sum(int(c.subs(N, n))*seq[n-j] for j, c in enumerate(given) if c != 0) == 0, (ident, n)
                if n <= E.degree():
                    boundaries += 1
            if args.source_dir:
                normalized, listed = read_source(args.source_dir / (ident + ".seq"))
                assert list(map(str, normalized)) == list(row.values()), ident
                assert listed == terms(b, k, ell, len(listed)), ident
            audited += 1
    assert audited == 80
    print(f"{audited} symbolic recurrence identities, {boundaries} exceptional starting indices checked directly.")
    print("Direct convolution and printed recurrences agree through n = 39 for every entry.")
    if args.source_dir:
        print(f"All source hashes, coefficient transcriptions, parameters and printed initial terms match OEIS {REVISION}.")


if __name__ == "__main__":
    main()
