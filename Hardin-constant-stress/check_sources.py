"""Compare the certificates with a checkout of the pinned OEIS export."""

import argparse
import ast
import hashlib
import json
import re
import subprocess
from pathlib import Path

import sympy as sp

from parity import median_count, six_count, six_layers
from verify import count_by_words, word_layers


x = sp.Symbol("x")
n = sp.Symbol("n", integer=True, positive=True)


def expression(s):
    """Read integer arithmetic, x, n and square roots without evaluating source code."""
    def visit(node):
        if isinstance(node, ast.Constant) and type(node.value) is int:
            return sp.Integer(node.value)
        if isinstance(node, ast.Name) and node.id in ("n", "x"):
            return {"x": x, "n": n}[node.id]
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.UAdd, ast.USub)):
            a = visit(node.operand)
            return a if isinstance(node.op, ast.UAdd) else -a
        if isinstance(node, ast.BinOp):
            a, b = visit(node.left), visit(node.right)
            if isinstance(node.op, ast.Add): return a + b
            if isinstance(node.op, ast.Sub): return a - b
            if isinstance(node.op, ast.Mult): return a * b
            if isinstance(node.op, ast.Div): return a / b
            if isinstance(node.op, ast.Pow): return a ** b
        if (isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and
                node.func.id == "sqrt" and len(node.args) == 1 and not node.keywords):
            return sp.sqrt(visit(node.args[0]))
        raise ValueError(f"Unknown expression syntax in {s}")
    return visit(ast.parse(s.replace("^", "**"), mode="eval").body)


def coefficients(formula):
    terms = re.split(r"a\(n\)\s*=", formula, maxsplit=1)[1].replace(" ", "").strip().rstrip(".")
    matches = list(re.finditer(r"([+-]?)(?:(\d+)\*)?a\(n-(\d+)\)", terms))
    assert matches and "".join(m[0] for m in matches) == terms, formula
    lags = {int(m[3]): (-1 if m[1] == "-" else 1)*int(m[2] or "1") for m in matches}
    return [1] + [-lags.get(i, 0) for i in range(1, max(lags)+1)]


def ogf(c, first):
    """The sequence begins at n=1. Multiply by the reciprocal characteristic polynomial."""
    degree = len(c) - 1
    assert len(first) >= degree
    den = sum(a*x**j for j, a in enumerate(c))
    num = sum(x**j * sum(c[i]*first[j-i-1] for i in range(j))
              for j in range(1, degree+1))
    return num/den


def lines_for(root, seq):
    return (root/"seq"/seq[:4]/(seq+".seq")).read_text().splitlines()


def formula_fields(lines):
    return [line[11:] for line in lines if line.startswith("%F ")]


def source_gf(fields):
    hit = next((s for s in fields if re.match(r"(?:Empirical )?[Gg]\.f\.:", s)), None)
    return expression(hit.split(": ", 1)[1].split(".")[0]) if hit else None


def check_source_files(root, attachment_dir):
    data = json.loads(Path(__file__).with_name("catalog.json").read_text())
    rev = subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip()
    assert rev == data["oeis_commit"], "The source checkout must match the pinned revision"
    recs = gfs = 0
    for t in data["tables"]:
        table = t["table"]
        fields = formula_fields(lines_for(root, table))
        proposed = next((l for l in fields if "apparently" in l.lower()), None)
        assert bool(proposed) == t["proposed"], table
        if proposed:
            degree = int(re.search(r"order (\d+)", proposed)[1])
            assert degree + 1 == len(data["polynomials"][t["polynomial"]]), table
        mapping = {k: (id, key) for k, id, key in t["columns"]}
        for k, layer in enumerate(word_layers(t["q"], t["d"], t["tilted"], max(mapping)), 1):
            if k not in mapping:
                continue
            id, key = mapping[k]
            lines = lines_for(root, id)
            fields = formula_fields(lines)
            if id == table:
                s = next(l for l in fields if l.startswith(f"k={k}: a(n)"))
            else:
                s = next((l for l in fields if re.match(r"Empirical:\s*a\(n\)\s*=", l)), None)
            if s is None:
                name = "a" + id[1:] + ".txt"
                assert any(name in l and "recurrence" in l.lower() for l in lines), id
                payload = ((attachment_dir if attachment_dir else root/"files"/id[:4])/name).read_bytes()
                assert hashlib.sha256(payload).hexdigest() == data["attachments"][name], id
                s = payload.decode("ascii")
            c = coefficients(s)
            assert c == data["polynomials"][key], id
            recs += 1
            gf = None if id == table else source_gf(fields)
            if gf is not None:
                terms = [count_by_words(j, layer, t["d"], t["tilted"]) for j in range(1, len(c))]
                assert sp.cancel(ogf(c, terms) - gf) == 0, id
                gfs += 1
    print(f"Matched {recs} stress recurrences and {gfs} rational generating functions to OEIS.")


def check_parity_sources(root):
    gfs = closed = 0
    for q, start in [(3, 235876), (4, 235885)]:
        for k in range(8):
            id = f"A{start+k}"
            fields = formula_fields(lines_for(root, id))
            c = coefficients(next(l for l in fields if l.startswith("Empirical: a(n)")))
            roots = sorted(({1, 2, 4, q} if k == 0 else {1, 2, q} if k > 1 else {2, q}))
            assert list(sp.Poly(sp.prod(x-a for a in roots), x).all_coeffs()) == c, id
            if k:
                vals = [median_count(j, k, q) for j in range(1, len(c))]
                assert sp.cancel(ogf(c, vals)-source_gf(fields)) == 0, id
                gf_expr = next(l for l in fields if l.startswith("a(n) ="))
                rhs = expression(gf_expr.split(" = ")[1].rstrip("."))
                assert sp.simplify(sp.expand_power_exp(rhs - median_count(n, k, q))) == 0, id
                gfs += 1
                closed += 1
    for k, layer in enumerate(six_layers(7), 1):
        id = f"A{234132+k}"
        fields = formula_fields(lines_for(root, id))
        c = coefficients(next(l for l in fields if l.startswith("Empirical: a(n)")))
        poly = (x-2)*(x**2-8) if k == 1 else (x-1)*(x-2)*(x**2-2)*(x**2-8)
        assert list(sp.Poly(poly, x).all_coeffs()) == c, id
        assert sp.cancel(ogf(c, [six_count(j, layer) for j in range(1, len(c))])-source_gf(fields)) == 0, id
        gfs += 1
        if k == 1:
            rhs = expression(next(l for l in fields if l.startswith("a(n) =")).split(" = ")[1].rstrip("."))
            h = sp.Symbol("h", integer=True, positive=True)
            for parity, want in [(0, 6*8**h+8*4**h), (1, 2*8**(h+1)+4*4**(h+1))]:
                assert sp.simplify(rhs.subs(n, 2*h+parity)-want) == 0, id
            closed += 1
    print(f"Matched 23 parity-family strip or diagonal recurrences, {gfs} generating functions "
          f"and {closed} closed forms to OEIS.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("oeisdata", type=Path)
    parser.add_argument("--attachments", type=Path, help="directory containing the six LFS texts")
    args = parser.parse_args()
    check_source_files(args.oeisdata, args.attachments)
    check_parity_sources(args.oeisdata)
