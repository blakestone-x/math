# A087412: a cubic congruence modulo powers of three

Blake Stone, developed with OpenAI Astra 6.2. November 26, 2026.

This package proves the conjecture attributed to Andrew Howroyd on July 17, 2018 in [OEIS A087412](https://oeis.org/A087412). Let

$$
a(N)=\#\{(x,y)\in\{0,\ldots,N-1\}^{2}:x^3+y^3\equiv1\pmod N\}.
$$

The pairs are ordered. Then, for every integer $e>1$,

$$
\boxed{a(3^e)=2\cdot3^e.}
$$

For example, the counts at moduli $9,27,81,243$ are $18,54,162,486$. The hypothesis $e>1$ is needed: $a(3)=3$.

## Proof

Write $e=k+2$ with $k\ge0$, and put $M=3^k$, so $3^e=9M$. Every residue modulo $9M$ has a unique representation $r+3u$ with $r\in\{0,1,2\}$ and $0\le u<3M$.

### 1. The possible residues modulo three

For every integer $u$,

$$
(r+3u)^3\equiv r^3\pmod9.
$$

The values $r^3\pmod9$ for $r=0,1,2$ are $0,1,8$. Among two such values, their sum is congruent to $1$ modulo $9$ exactly for the ordered pairs $(0,1)$ and $(1,0)$. Since $9\mid9M$, every solution of the original congruence therefore belongs to precisely one of the disjoint cases

$$
(x,y)=(3u,1+3v)\quad\text{or}\quad(x,y)=(1+3u,3v),
\qquad 0\le u,v<3M.
$$

The two cases have equal cardinality by swapping the coordinates.

### 2. A permutation polynomial

Define

$$
F(t)=t+3t^2+3t^3.
$$

For any $s,t$,

$$
F(s)-F(t)=(s-t)\bigl[1+3(s+t+s^2+st+t^2)\bigr].
$$

The bracket is congruent to $1$ modulo $3$, hence is invertible modulo $M=3^k$. It follows that $F(s)\equiv F(t)\pmod M$ implies $s\equiv t\pmod M$. Thus $F$ is injective on the finite ring $\mathbb Z/M\mathbb Z$, and consequently is bijective. When $k=0$, this ring has one element and the same conclusion holds.

The Lean proof verifies invertibility without an unproved number-theoretic hypothesis: $3$ is nilpotent in $\mathbb Z/3^k\mathbb Z$, and $1$ plus a nilpotent element is a unit. Equivalently, the inverse of $1+w$ is the finite geometric sum $1-w+w^2-\cdots+(-w)^{k-1}$ when $w^k=0$ and $k>0$.

### 3. Count one of the two cases

For the first case, direct expansion gives

$$
(3u)^3+(1+3v)^3-1=9\bigl(3u^3+F(v)\bigr).
$$

The congruence modulo $9M$ is therefore equivalent to

$$
F(v)\equiv-3u^3\pmod M.
$$

Fix any $u$ with $0\le u<3M$. The permutation property provides exactly one solution $v_0$ modulo $M$. Among $0\le v<3M$, the solutions are exactly

$$
v_0,\quad v_0+M,\quad v_0+2M.
$$

There are $3M$ choices of $u$ and three choices of $v$ for each, giving $9M$ solutions in this case. The second case contributes another $9M$, so

$$
a(3^e)=18M=2\cdot3^e.
$$

This proves the formula for every exponent in its stated domain.

## Formal theorem and correspondence

`Proof.lean` defines `a N` as the sum of indicators over all ordered pairs in `Fin N × Fin N`. It uses `Nat.ModEq`, so the equation means equality of residues modulo $N$, including the usual interpretation at $N=1$.

The theorem `A087412.original_count` proves that this sum equals the cardinality of the literal solution subtype. The final theorem is:

```lean
theorem original_conjecture (e : ℕ) (he : 1 < e) :
    Fintype.card {xy : Fin (3^e) × Fin (3^e) //
      xy.1.val^3+xy.2.val^3 ≡ 1 [MOD 3^e]} = 2*3^e
```

The equivalent sequence theorem is `A087412.conjecture`. Both are unconditional apart from the displayed exponent bound. The finite sum decomposition and its unique residue representations are proved using `finProdFinEquiv`; no count formula is assumed. The proof covers all exponents, rather than stopping at a finite computational range.

The main intermediate theorems are:

| Theorem | Content |
| --- | --- |
| `F_injective`, `F_bijective` | $F$ permutes every ring $\mathbb Z/3^k\mathbb Z$. |
| `F_sum` | Each normalized one-variable congruence has exactly one solution modulo $3^k$. |
| `residue_cases`, `solution_split` | The two residue patterns are the complete possibilities. |
| `equation_normalized` | The cubic congruence reduces to $F(v)+3u^3\equiv0$. |
| `count_normalized` | Exact finite sum decomposition into the two equally sized cases. |
| `F_sum_lift` | Each normalized root has exactly three lifts to the required interval. |
| `conjecture`, `original_conjecture` | The formula for every $e>1$. |

All checked theorem dependencies are the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`. There are no placeholders, `sorry`, `admit`, additional axioms, or `native_decide` calls.

## Reproduce the kernel check

The package pins Lean 4.19.0 and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b` (v4.19.0), with a committed dependency manifest. With `elan` installed:

```sh
lake exe cache get
lake build
lake env lean Proof.lean
```

`verification.txt` records a fresh build of the packaged source and its printed axiom dependencies. The independent review is recorded separately in `AUDIT.md` and `audit-verification.txt`.

The optional command `python3 examples.py` enumerates the original ordered pairs at five small powers of three. Those examples are separate from the proof.

## Source status and prior work

- The [OEIS entry](https://oeis.org/A087412) credits the sequence to Yuval Dekel (October 21, 2003), and the conjecture at powers of three to Andrew Howroyd (July 17, 2018).
- The [official OEIS-maintained raw export](https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A087/A087412.seq), retrieved during this session on November 26, 2026 in America/Chicago, is preserved as `source.seq`. It identifies revision **#30, September 17, 2019, 12:03:03**, and still labels this exact formula a conjecture.
- The entry already states other formulas at prime powers, including the nonsingular case $p\ne3$. Those formulas are prior work. This package addresses the separately labeled $p=3$ conjecture.
- Searches for the exact sequence identifier, the two-cube congruence at powers of three, and the [trureturing](https://www.trureturing.org/conjectures), [Fabian Arevalo](https://fabianarevalo.com/math), and [Eppie/OEIS proofs](https://github.com/Eppie/oeis-proofs) collections did not locate an earlier proof of this exact formula. Related material about three cubes, integral Fermat equations, and the ternary norm form $x^3+y^3+z^3-3xyz$ concerns different equations.

The elementary permutation and lifting arguments use standard algebra. The priority statement is limited to the sources searched: the entry remains conjectural there and no earlier exact proof was located. This is not a claim that all literature has been exhausted or that the background algebra is new.
