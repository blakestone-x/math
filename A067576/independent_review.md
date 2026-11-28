# Independent review: A067576

**Decision: PASS.** Reviewed November 27, 2026 by the sequence-lane reviewer, who did not author this package. No edits to the theorem sources or configuration were requested or made.

## Source fidelity and exact scope

I independently fetched the immutable OEIS-data source at commit `eb3c646fa1194774d4a21422a028616eaf549691`. Its 2,333 bytes match `sources/A067576.seq` exactly, with SHA-256 `5fc8472d8dc9c5b2afe7e374bc5261150bf3d5cdaff75d0effe24746268ee8ab`. The source's title and printed array specify the increasing positive integers with a prescribed number of binary ones. Kimberling's November 8, 2025 comment explicitly conjectures eventual doubling after adding one to each array entry.

The package preserves both positive indices. Its `weight` is literally `Nat.bitIndices.length`, and `entry i j` is the `(j-1)`st zero-based `Nat.nth` value satisfying that weight. The positive-row infinitude, membership, positivity, strict monotonicity, and predecessor count are proved. Consequently the mathematical endpoints refer to the actual increasing source enumeration, rather than relying on `Nat.nth`'s fallback outside its genuine range.

The original comment's wording for `d(k)` is loose. The package explicitly defines the starting point as the least positive row from which every subsequent transition doubles, and its first values `1,1,2,3,4` agree with the source. It does not confuse that row number with the value in the corresponding column. The internal row zero is used only for base cases; the public source assertion uses positive rows and columns.

The resolved statement is one source family: eventual doubling of every shifted column. The explicit formula and sharp onset are proved components of that result, not additional problem counts.

## Mathematical review

I read all four Lean modules and the complete human manuscript. The reasoning is sound:

1. `Binary.lean` derives the even/odd weight identities from the literal bit-index representation. It proves the minimum-value bound, all-ones weight, the exact even/odd prefix-count identities, and the rank of `2^(i+1)-2` without assuming the target formula.
2. `Columns.lean` proves simultaneously that `(2^(k+1)-1)2^d-1` has weight `k+d` and exactly `k` smaller numbers of that weight. `Nat.nth_count` then identifies the genuine source entry. The substitution `k=j-1`, `d=i+1-j` is guarded by the necessary hypotheses. The closed form proves doubling throughout the claimed region.
3. `Sharp.lean` proves the independent leading-bit prefix-count identity and identifies the preceding-row value `T(k+1,k+3)+1=5·2^k`. The next-row value is `2^(k+3)-1`, so their transition fails to double. The proof of `IsLeast` uses that failure for every `j≥3` and handles `j=1,2` through positivity of the proposed onset. It proves minimality, not only a sufficient bound.
4. `Proof.lean` collects the source specification and the universal endpoint. All quantified ranges agree with the manuscript. The formal closed-form theorem also covers a harmless internal zero-row base instance, while the prose source result is restricted to positive rows.

I checked the manuscript's prefix-count decompositions, boundary values, and the failure calculation independently. The theorem/lemma/proof/equation environments are balanced. No mathematical or indexing correction was needed.

## Independent build and finite replay

The independent build copied only the four source modules and pinned configuration into a fresh directory, sharing only the pinned external dependency cache. All four explicit default roots compiled successfully with Lean 4.19.0 and mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`; `independent_build.log` records **exit code 0**. All audited declarations use only `propext`, `Classical.choice`, and `Quot.sound`.

Afterward I recomputed every proof/configuration hash recorded in that log. All matched, so the reviewed files remained unchanged. No `sorry`, `admit`, custom axiom, or `native_decide` occurs in the theorem sources.

As a separate indexing check, I directly enumerated every positive integer below `2^18` and grouped it by Python's `bit_count()`. This used neither the package's fixed-weight successor generator nor the proposed recurrence. It reproduced all 66 displayed antidiagonal source terms, 171 closed-form instances, 153 doubling transitions, and all 16 preceding-row failures available for columns 3 through 18. `independent_replay.json` records the results. These finite checks supplement the unbounded Lean proof.

## Provenance assessment

I read the bounded search dossier and independently fetched the current-observed open-math-agents statement at commit `3a0039bdf1da87d3915b73dabafd68415871f2e4`. It indeed uses the same literal `Nat.nth` definition and poses the exact least-onset theorem, with the proof left as `sorry`. The package correctly credits this earlier formulation and does not represent it as a completed prior proof.

I also opened the primary Dobrić–Skyers–Stanley paper, arXiv:1603.04896, and inspected the relevant weight-ranking section, including Lemma 3, Definition 5, and Corollary 3. It supplies the classical ranking/unranking framework and its polynomial-time result; the inspected statements do not assert eventual column doubling or the sharp onset. The package credits that framework and the prior special cases in A036563/A066884.

The broad semantic search's trureturing-pages `research-news.json` hit was independently fetched and screened; it did not contain A067576 or an eventual-geometric assertion for this array. The recorded global and scoped searches remain bounded, and the package appropriately avoids a worldwide-priority claim.

**Conclusion:** the exact source conjecture, the original array interpretation, the closed form, and the minimum onset are supported by a complete unbounded proof and a successful independent source-only build. No outstanding review issue remains.
