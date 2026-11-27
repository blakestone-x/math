# Independent audit: A288668 / A288665

**Result: PASS.** A reviewer separate from the author read the complete formal proof, the explanatory manuscript, the source review, and the preserved primary records, and compiled an independent fresh copy of the package on November 27, 2026.

Audited `Proof.lean` SHA-256:

```text
a57dbbfaca953f3b188309ff37cf285824011feeae14dd2ab593a2cddd05f860
```

## Statement fidelity and mathematical review

The formal rewrite scans left to right, replaces nonoverlapping `00` by `0110` and `10` by `000`, and copies letters that do not start a matching pair. Its initial word is exactly `00`. This agrees with the explicit rule in A288665 and the conjectural length interpretation in A288668.

The three tokens encode `00`, `0110`, and `01000`. Their substitutions are respectively `B`, `C`, and `AAB`. The key lemma `rewrite_code_append` holds with an arbitrary binary suffix, so it genuinely prevents boundary-crossing rewrites; it is stronger than a check of the three isolated token images. The decoded token iteration is proved equal to every literal binary iterate.

The all-index concatenation identity is correctly deduced from the third token iterate and preservation of concatenation on the decoded language. Consequently the length recurrence is

$$
L_{n+3}=L_{n+1}+2L_n,\qquad (L_0,L_1,L_2)=(2,4,5).
$$

The equality with the independently defined recurrence sequence is proved for every natural index. The weighted recurrence, nested-prefix statements, and exponential lower bound follow from the same word identity. They are consequences of one recorded assertion, not separately counted conjecture resolutions.

The generating functions in the README follow by multiplying the order-three recurrence and substituting the displayed initial values. They are explicitly presented as mathematical consequences rather than additional Lean theorems. The prose discussion of limiting words follows from the proved nested prefixes and unbounded lengths; no formal construction of an infinite word is claimed.

## Source ambiguities

A288668 has inconsistent prose initial-index labels. Its data, offset, generating function, and executable recurrence program agree on the initial values at indices 0, 1, and 2. The formal definition uses that coherent convention and explicitly documents the discrepancy. The clerical indexing error is not counted as a disproof. Mistyped related-entry cross-references are also documented without being counted as mathematical results.

The prior-work review distinguishes previously treated Kimberling systems by their actual replacement rules. Neither the repository's earlier pair-rule family nor the separately published A288476/A288473/A288551 system has the same rewrite rule as this target.

## Independent verification

A new temporary package was populated from the exact source and pinned configuration. Only external dependency caches were reused; the local proof object was rebuilt from scratch with `lake build`. The build passed under Lean 4.19.0 and mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The full output and source hashes are in `audit-verification.txt`.

Inspection found no admissions, extra axioms, unsafe declarations, or native-evaluation proof shortcuts. Printed theorem dependencies are limited to `propext`, `Quot.sound`, and, for the arithmetic growth estimate, `Classical.choice`. No mathematical or source-scope correction was required.
