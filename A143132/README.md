# A143132: the conjectured period of the last decimal digit

**Blake Stone** · Proof developed with OpenAI Astra 6.2 · November 26, 2026

## Statement and source

OEIS A143132 is the binomial transform of the finite sequence
`1, 5, 15, 35, 70`, continued by zeros, with its first term indexed by 1.
Its comment conjectures the repeating last-digit pattern `1, 6, 6, 6`.
The entry was created by Gary W. Adamson on July 27, 2008. The current
entry still marks the last-digit statement as a conjecture.

Primary source: <https://oeis.org/A143132>.

We prove, for every integer n >= 1,

$$
a(n)\bmod 10=
\begin{cases}
1,& n\equiv1\pmod4,\\
6,& \text{otherwise}.
\end{cases}
$$

## Proof

Use a zero-based index, writing b(m)=a(m+1). By the definition of the
binomial transform,

$$
b(m)=1+5m+15\binom m2+35\binom m3+70\binom m4.
$$

Repeated application of Pascal's identity, equivalently Vandermonde's
identity with an increment of four, gives the exact integer identity

$$
b(m+4)-b(m)
=10\left(32+55m+56\binom m2+28\binom m3\right).
$$

For completeness, the coefficients of 1, m, binom(m,2), binom(m,3)
in this difference are respectively 320, 550, 560, and 280; the
binom(m,4) terms cancel. The identity holds even for m < 4, using the
usual convention binom(m,k)=0 when k>m.

Consequently b(m+4) and b(m) have the same residue modulo 10 for every
m >= 0. The initial values b(0), b(1), b(2), b(3) are 1, 6, 26, 96.
Reducing them modulo 10 and applying the period relation proves the
claim for every index.

## Formal verification

The Lean file `Proof.lean` defines the original finite binomial
transform, proves the exact four-step difference identity, proves
periodicity, and proves the correctly shifted OEIS theorem
`A143132.conjecture` for all positive indices.

It was checked with Lean 4.19.0 and mathlib v4.19.0, commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`.
The only imported mathlib module is `Mathlib.Data.Nat.Choose.Basic`.
The kernel reports only the standard axioms `propext`, `Classical.choice`,
and `Quot.sound`. There are no placeholders, added axioms, or
`native_decide` uses.

## Prior work and scope

This is an elementary congruence consequence of the sequence's existing
explicit description. The OEIS already includes a generating function
and formulas supplied by R. J. Mathar and T. D. Noe in 2008, including a
quartic polynomial formula. Those formulas are prior work, and the
present result does not claim them as new.

Checks on November 26, 2026 found the exact last-digit assertion still
marked conjectural. Exact-ID searches for proofs, theorems, and Lean
formalizations, together with searches of the public trureturing,
Fabian Arevalo, and Eppie material, did not locate a previous proof of
the stated congruence. This is a description of the search performed,
not an assertion that no proof exists anywhere.


## Reproduce the verification

From this directory, using Elan to select the pinned Lean toolchain, run:

```sh
lake exe cache get
lake build
```

`lakefile.lean` pins mathlib to its v4.19.0 commit, and
`lake-manifest.json` locks its transitive dependencies. The package
includes `verification.txt` from a fresh build of these exact sources,
plus an independent review in `AUDIT.md` and `audit-verification.txt`.
No network access is needed after the dependency source and compiled
cache have been obtained.

## Collected proof document

[Read the complete proof collection (PDF)](../notes/Math_Proofs_Batch4.pdf) · [LaTeX source](../notes/Math_Proofs_Batch4.tex)
