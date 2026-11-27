# Source, scope, and bounded prior-resolution checks

Checked on **2026-11-27**. These checks establish the public statement and identify nearby prior results. They do not establish first-publication priority or exclude private, unindexed, or differently phrased proofs.

## Exact primary source

- [OEIS A211417](https://oeis.org/A211417), COMMENTS by Peter Bala, **2025-08-28**.
- Current official export: [oeis/oeisdata, seq/A211/A211417.seq](https://github.com/oeis/oeisdata/blob/main/seq/A211/A211417.seq).
- The checked entry is revision **94**, timestamp **2026-08-26 01:12:34**.
- Git blob: **d0f348463c143fc227c5e0cbafaa2b49732312bb**.
- Immutable export commit: **dff800c40a409482c9b734eecd1958986302e385**, committed 2026-09-10.
- [Immutable source link](https://github.com/oeis/oeisdata/blob/dff800c40a409482c9b734eecd1958986302e385/seq/A211/A211417.seq).
- The current and immutable contents were separately retrieved and compared byte for byte: both contain **5,944 UTF-8 bytes** and match.
- Archived bytes: `sources/A211417.seq`, SHA-256 **a75083c938bfac328fa90aeabb3e0fd0d50313e1e2e948fa837e2dfdf409cb93**.

The sequence is the factorial ratio

\[
A(n)=\frac{(30n)!n!}{(15n)!(10n)!(6n)!},\qquad n\ge0.
\]

The source's generalized positive-shift assertion asks: for each \(k=2,3,5\) and \(r\ge1\), does a positive constant \(C(k,r)\), independent of \(n\), make

\[
\frac{C(k,r)A(n)}{\prod_{1\le i\le r,\ \gcd(i,k)=1}(kn+i)}
\]

an integer for every \(n\)? This exact clause remains conjectural in the checked export. The package proves it with the explicit integer \(C(k,r)=((30r)!)^r\), and also covers \(r=0\).

## Results excluded from the new claim

1. **Integrality of the unmodified factorial ratio.** This is classical and is explained by Peter Bala's [OEIS proof note](https://oeis.org/A211417/a211417_1.txt); the entry also cites Bober's classification of integral factorial ratios. The present Lean proof re-establishes it only to connect natural division to the exact rational definition.
2. **The divisor \(30n-1\).** The OEIS entry credits the AlphaProof Nexus proof. See [its Lean source](https://github.com/google-deepmind/alphaproof-nexus-results/blob/main/APNOutputs/OEIS/oeis_a211417_conjecture_specific.lean) and Adamczewski, [OEIS Open](https://arxiv.org/abs/2608.11941), Appendix A. This is not the family proved here.
3. **The four fixed-factor divisibility statements.** Kenta Kitamura's [oeis-a211417 repository](https://github.com/KitaKen1/oeis-a211417) has kernel-checked proofs of \((2n+1)\mid7A(n)\), \((3n+1)\mid A(n)\), \((5n+1)\mid A(n)\), and their product dividing \(42A(n)\). The scope was checked directly in its README (blob **0d07d5c847dd0b46e412942672346a41173b436c**) and [Formal Conjectures PR 5010](https://github.com/google-deepmind/formal-conjectures/pull/5010). No new claim is made for those fixed cases.
4. **The generalized negative-shift \(D(r)\) family.** [Formal Conjectures issue 4923](https://github.com/google-deepmind/formal-conjectures/issues/4923) records a paper-complete proof with an explicit positive witness \(D(r)=\operatorname{lcm}(1,\ldots,r)^{|\{1\le i\le r:\gcd(i,30)=1\}|}\). Searches also located the title *Bala's D(r) Divisibility Conjecture for A211417: a Proof with an Explicit Constant*. This concerns factors \(30n-i\); it is excluded from the present contribution. The issue also explains that a formal existential allowing \(D=0\) would be vacuous. Here the formal theorem explicitly requires and proves **\(C>0\)**.
5. **Supercongruences.** These are separate source assertions and are outside this package's scope.

No proof code from these prior projects is imported, copied, or depended on. The current proof uses mathlib's standard natural-number valuations, factorial formula, and finite-sum infrastructure.

## Bounded searches performed

Both web search systems were used. The searches included exact identifiers, the precise generalized notation, and semantic variants, including:

```text
"A211417" "C(k" proof
"A211417" "C(k, r)"
"A211417" "C(k,r)" proof
"A211417" "C(2" proof
"A211417" "2*n + i"
"A211417" "positive" "shift"
"A211417" "positive-shift"
"A211417" "shifted"
"A211417" "uniform" "integrality"
"A211417" "general" "Bala" integrality
"Chebyshev numbers" "integrality" "shift" conjecture
"factorial ratio" "2n+1" "30n" integrality
"A211417" "D(r)"
"Bala's D(r) Divisibility Conjecture"
```

The searches located the source and the distinct prior work listed above. They did not locate a proof of the arbitrary positive-shift family for all \(r\).

The live [trureturing conjecture catalog](https://www.trureturing.org/conjectures), reporting **2,235 resolved results**, was directly opened and searched for `A211417`; no matching entry was returned. The search index also exposes a trureturing book reference to the four already-known fixed statements, which was treated as prior work rather than as evidence about the generalized clause. GitHub issue searches for `repo:the-omega-institute/trureturing A211417` and a narrowed `"C(k"` query returned references to fractional-index factorial ratios and other arithmetic sequences; none returned a proof of this positive-shift family. Those issue searches are bounded discovery checks, not a claim to have read every issue or comment in the repository.

## Source-to-formalization obligations

The source uses ordinary factorials at nonnegative integer indices, so no Gamma-function convention is involved. Every selected shift factor is positive, including at \(n=0\). The finite set in Lean is exactly `((Finset.Icc 1 r).filter (Nat.Coprime · k))`.

`factorial_ratio_identity` proves that the natural quotient is exact; `sourceRatio_eq_a` connects it to the literal rational expression. `positive_shift_rational_integrality` then constructs an integer equal to the requested quotient. The proof controls valuations of the **entire product**, counting every divisible factor at every prime-power level. It does not infer product divisibility merely from separate divisibility of each factor.

The formula for \(C\) is positive for every \(r\), depends only on \(r\), and is not defined using a supremum, unknown sequence, or existential placeholder. The arbitrary-\(n\) theorem has no computation bound. The 30-period calculation is a universal floor-arithmetic lemma used within the infinite argument.
