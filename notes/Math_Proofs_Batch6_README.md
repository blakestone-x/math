# Eight sequence assertions: negabinary, divisor sums, and tetration

**Blake Stone** · Proof developed with OpenAI Astra 6.2 · November 26, 2026

[Read the collected manuscript](Math_Proofs_Batch6.pdf) · [LaTeX source](Math_Proofs_Batch6.tex)

This collection resolves **eight recorded assertions across five OEIS entries: seven proofs and one disproof**. The five standalone packages contain **six Lean proof modules**. Each package includes a full written proof, the exact formal source, pinned dependencies, primary source snapshots, a fresh package-build log, an independent audit and compilation log, and SHA-256 checksums.

## Results and navigation

| Package | Recorded assertions resolved | Main formal declarations |
|---|---|---|
| [A016789 — negabinary XOR](../A016789/README.md) | **1 proved:** the three-way XOR of n and the binary encodings of the negabinary representations of ±(n+1) is 3n+2, for every n≥0. | `A016789.original_conjecture` |
| [A300984 — two squarefree divisor sums](../A300984/README.md) | **1 proved:** every member has the form 2^i·p^j. Stronger necessary conditions give i,j≥2, p≡1 modulo 12, squarefree 3(p+1), and n≥676. | `A300984.conjecture`, `strengthened_conjecture`, `member_ge_676` |
| [A324017 — modular tetration](../A324017/README.md) | **2 proved, 1 refuted:** the fixed-point and quotient congruences hold; the claimed additional digit of stability fails at m=n=2, j=27. | `A324017.fixed_point`, `quotient_conjecture`, `third_claim_false` |
| [A389524 — divisor-count triangle](../A389524/README.md) | **2 proved:** Conjectures 1 and 3, giving row sums d(n) and the diagonal T(2n,n)=n−d(n), for every n≥1. | `A389524.row_sum`, `diagonal` |
| [A393833 — palindromic divisor residues](../A393833/README.md) | **1 proved:** an eligible integer exists at every positive index, with exactly the prescribed divisor count and a palindromic ordered proper-divisor residue list. | `A393833.conjecture`, `exists_least` |

A389524 contains `Uchimura.lean` and `Proof.lean`; each other package contains one `Proof.lean`. Auxiliary identities and stronger consequences are not counted as additional recorded conjectures.

## Precise scope

**A016789** begins with the standard binary digit list evaluated in base −2. Existence and uniqueness of the positive and negative codes are proved before the XOR theorem. Its two companion XOR identities support the single recorded conjecture.

**A300984** begins with both literal divisor sums. The strengthened conditions are necessary, not a converse characterization or an infinitude theorem. The separate OEIS claim about the proportion of relevant primes in A082539 is unaddressed. The universal lower bound 676 is formal; the README separately checks membership of 676 by explicit arithmetic.

**A324017** uses the original integer power towers. Its disproof uses the canonical least residue: 3³≡27 modulo 64, whereas 3²⁷≡59 modulo 64. The valid replacement preserves the first m base-2n digits when the tower height increases; it is not counted as another conjecture. The inconsistent array indices in the source examples are documented separately from the literal claim being refuted.

**A389524** defines the original recursive triangle and derives its columns. The finite form of Uchimura's identity is proved in the companion module, so no q-series identity or convergence premise is assumed. Conjecture 2, the weighted orphan-count identity, is expressly unclaimed.

**A393833** proves existence and arbitrarily large witnesses, together with existence of a least eligible integer. Its prime-power witnesses need not be minimal. No formula for the minimum or new sequence values is claimed. Constant palindromes are permitted by the source, and the n=1 case is included.

## Classical ingredients and source status

The packages credit established mathematics: negabinary representations and conversion methods described by Jörg Arndt; the squarefree-divisor product recorded by Vladeta Jovovic and Walter Kehowski's two-odd-prime obstruction; modular exponential lifting and stabilization studied by Daniel B. Shapiro and S. David Shapiro, and by Jiménez Urroz and Yebra; Uchimura's divisor identity and the work of Bressoud and Subbarao; and the classical existence of arbitrarily large primes congruent to one, available in mathlib through an elementary cyclotomic proof.

The contribution is the explicit resolution and formal verification of these selected assertions from their original definitions. The package `source_checks.md` files record the primary sources, related work, and bounded searches for prior resolutions. Conjecture labels remained in the retrieved source snapshots. This is not a claim of exhaustive historical priority or OEIS editorial acceptance, and the classical ingredients are not presented as new general theories.

## Reproduce and verify

Every package pins **Lean 4.19.0** and mathlib commit **`c44e0c8ee63ca166450922a373c7409c5d26b00b`**. With Elan selecting the included toolchain, run from any individual package directory:

```sh
lake exe cache get
lake build
```

The included `lake-manifest.json` pins transitive dependencies. The exact final proof sources have passed both a fresh package build and a separate isolated compilation. Public theorem reports contain only `propext`, `Classical.choice`, and `Quot.sound`; there are no unfinished proofs, custom axioms, or `native_decide` calls.

Each `verification.txt` records the package build. `AUDIT.md` and `audit-verification.txt` record the independent review and compilation. To verify all delivered package files against their checksums, run in that package directory:

```sh
sha256sum -c SHA256SUMS.txt
```

Each checksum manifest covers all regular package deliverables, including nested source snapshots, and excludes only the checksum manifest itself. Build caches and compiled artifacts are outside the delivered packages.
