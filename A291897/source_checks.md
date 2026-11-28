# A291897: source fidelity and bounded prior-work checks

Recorded November 27-28, 2026; recovered and checked again November 28. This report distinguishes an exact recorded assertion from classical background and nearby questions. It is not a worldwide-priority certificate.

## Selected assertion and immutable source

The official OEIS data snapshot at commit `091a90f51479669655f4e46343867ea2abd5d4ff` defines A291897 as the reduced numerator of `E_(2n−1)(n)`, with offset one, and records the conjecture that `(2n−1)²` divides every term. The entry credits Vladimir Shevelev, September 22, 2017. Its revision header is number 48, July 8, 2022. The local snapshot has SHA-256 `ae128d1e6038f8c1e7d7f9d4debd37bec241b14b607689f394e4d9ead2b6f785`.

The final theorem is for every positive natural `n`, with the integer expression `2*n−1` and rational reduced numerator. It does not substitute a formula for the desired divisibility as the sequence definition. The finite source check matches all 15 frozen terms. The neighboring A292911 snapshot is retained only to document the excluded cubic-divisibility question.

## Classical source representation

[NIST DLMF 24.2](https://dlmf.nist.gov/24.2) gives the signed Euler-number convention, vanishing of odd Euler numbers, and centered expansion in formula 24.2.10. [DLMF 24.5.4](https://dlmf.nist.gov/24.5#E4) gives the even-number recurrence. These pages were read during the proof and reopened after recovery. The formal value is defined by this finite expansion. The manuscript derives its equivalence to the usual exponential-generating-function convention; that analytic equivalence is not separately formalized in Lean.

The independent reviewer also inspected the Euler-number and Euler-polynomial portions of Carlitz, *A Note on Euler Numbers and Polynomials* (1954), [DOI 10.1017/S0027763000018043](https://doi.org/10.1017/S0027763000018043). Its centered expansion is relevant classical background. The inspected congruences have different hypotheses and do not supply the selected all-positive-index assertion in the form proved here. This is a bounded reading judgment, not a claim that every consequence of that literature has been exhausted.

## Source-linked paper and admitted formal statement

- Vladimir Shevelev, [*On a Luschny question*, arXiv:1708.08096v3](https://arxiv.org/abs/1708.08096v3), was read in full during the original work. Its five pages concern the denominator of `E_n(x)−E_n(1)`, a different question. Its abstract and version information were reread after recovery.
- The [open-math-agents statement](https://github.com/GuillaumeBAUD-coder/open-math-agents/blob/5494b7a26d84a2fe7ab23ca2e45e1e864f5714f9/statements/oeis-a291897.lean) was inspected at that immutable commit. It uses the same centered source representation, credits `@DhruRules`, and leaves the target theorem admitted. That source-formalization credit is retained. Our proof does not import the admitted file.
- `facebookresearch/atlas-lean` at commit `30b3ab2d7dd613f446ff372cd98cfdedf3b47abe`, file `MathlibExtTest/NumberTheory/Bernoulli/EulerValueSumModPrime.lean`, concerns sums of Euler values at zero modulo a prime. It is a different assertion.
- `seanm27lol/left-to-solve-research` at commit `0777dbe2a910c5564e13c2278bae6547f2ace5be`, notes `06-own.md` and `12-discrete.md`, was inspected for semantic Euler hits; the relevant hits concern products or circuits, not this numerator assertion.
- `kolinhuang0427/open-math-results` at commit `f4fea05c78ea954ace0f1d51da6c9c189e68ccf0` had no exact A291897 hit in the inspected search. Its A250917 and A132411 proof files concern different uses of Euler operators or series.

## Search scope and conclusion

The original screening used both available web search engines for the exact identifier and variants involving Shevelev, Euler-polynomial numerators, odd degrees and square divisibility. GitHub searches included exact Lean/Markdown identifier searches and the repositories above, `trureturing`, `1337isnot1337/solved-conjectures`, and the destination repository. Exact mathematical hits were distinguished from incidental hexadecimal strings. No complete earlier proof of the selected assertion was found in the inspected results. Classical Euler formulas were credited rather than counted as new results.

After workspace recovery, exact and semantic web queries were repeated and the DLMF pages and source-linked paper metadata reread. The fresh retrieval receipt is stored in `sources/recovery_search_receipt.json`; it explicitly includes any retrieval failures. The original lost raw search logs are not presented as fresh logs or reconstructed byte-for-byte receipts.

The result reported by this package is a proved recorded OEIS assertion, with a general odd-degree lemma. No claim is made that all literature has been searched or that the proof is the first possible derivation from classical formulas.
