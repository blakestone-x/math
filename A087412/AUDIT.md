# Independent audit: A087412

**Date:** November 26, 2026 (America/Chicago)  
**Reviewer:** independent AI review, separate from the proof authoring process  
**Result:** passed mathematical review, definition review, and fresh Lean compilation.

## Exact reviewed sources

- `Proof.lean` SHA-256: `6cb09cbc47175fad13ef5416a55ad9e72fdf9cd0e19db52f30b5cdfe0bc883ca`.
- `source.seq` SHA-256: `067f9038381aadb26c052439397604d3b6681df26283d6f5cacf15fe905dff3e`.
- `README.md` was checked against both the formal theorem and the source snapshot.

The primary source is [OEIS A087412](https://oeis.org/A087412). The preserved
export identifies revision 30, September 17, 2019, and explicitly labels
Andrew Howroyd's formula `a(3^e)=2*3^e` for `e>1` as a conjecture.

## Statement fidelity

The source counts solutions of `x^3+y^3 ≡ 1 (mod N)`. Its supplied programs
loop independently over `x,y=0,...,N−1`, confirming that the pairs are
ordered and that zero residues are included. The Lean definition `a N`
uses exactly these two finite ranges, represented by `Fin N`, and an
indicator for that same congruence. It does not quotient by swapping
coordinates or exclude any residue classes.

`original_count` proves, rather than assumes, equality of the indicator
sum with the cardinality of the literal subtype of ordered pairs satisfying
the congruence. `original_conjecture` states the final result directly for
that subtype, for every natural exponent `e` with `1<e`. There is no bound
on the exponent and no extra arithmetic hypothesis.

## Mathematical review

1. The reduction modulo nine is complete. The cubes of residues zero,
   one, and two modulo three are respectively zero, one, and eight modulo
   nine. Their sum is one only in the ordered cases `(0,1)` and `(1,0)`.
   This produces two disjoint solution classes.
2. For `F(t)=t+3t²+3t³`, the exact difference factorization is correct.
   The multiplier is one plus a multiple of three. In `ZMod (3^k)`, three
   is nilpotent, so this multiplier is a unit. Cancellation proves
   injectivity, and finiteness proves bijectivity.
3. The expansion `(3u)^3+(1+3v)^3−1=9(3u³+F(v))` is correct. Cancelling
   the common factor nine in the modulus is formally proved using
   `Nat.ModEq`, not assumed as an informal division step.
4. The finite decompositions use the explicit bijection
   `Fin M × Fin N ≃ Fin (M*N)`. All reordering and summation factors are
   justified. In particular, each normalized root modulo `M` has three
   representatives in `Fin (3*M)`, there are `3*M` choices of the other
   coordinate, and there are two disjoint coordinate patterns. The
   resulting count is `2*(3*M)*3=18*M=2*3^(k+2)`.
5. The boundary `e=2` is covered by `k=0`, `M=1`. The one-element residue
   ring and the three representatives in `Fin 3` are handled by the same
   proof. There is no hidden use of `k>0`. The source correctly excludes
   `e=1`, where the count is three instead of six.
6. The README proof agrees with the formal argument. The optional
   examples are illustrative only; the theorem does not depend on them.

## Independent kernel check

A separate invocation of the pinned `lake env lean` compiled the exact
packaged `Proof.lean` to a new audit object file. Its SHA-256 was checked
before and after compilation and did not change. The process exited
successfully with code zero. The full command and compiler output are
recorded in `audit-verification.txt`.

The four printed declarations (`F_injective`, `original_count`,
`conjecture`, and `original_conjecture`) depend only on the standard Lean
axioms `propext`, `Classical.choice`, and `Quot.sound`. The reviewed source
contains no added axioms, placeholders, `sorry`, or `native_decide` calls.

The project pins Lean 4.19.0 and mathlib commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`.

## Scope

This audit verifies the mathematical statement, its correspondence to the
preserved OEIS definition, and the reproducible formal proof. The source
snapshot establishes that this particular OEIS revision retains the
conjectural label. The bounded prior-work search is described in the
README; neither this audit nor a successful Lean build establishes
absolute publication priority.
