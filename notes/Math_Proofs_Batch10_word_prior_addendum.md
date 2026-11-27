# Extended prior screen for the Batch 10 rewriting results

Checked 2026-11-27 through the connected GitHub code search, in addition to the
already preserved two-engine web, primary OEIS, paper, and trureturing checks.
These are bounded searches, not a certificate of worldwide priority.

## Direct ProveIt queries

Separate searches for `A289128`, `A289129`, `A289130`, and `A289131` restricted to
`VladimirReshetnikov/ProveIt` each succeeded and returned no results.

Semantic searches in the same repository:

- `"StringReplace" "0010" "011" "010"`: no results.
- `"Kimberling" "nonconvergence"`: no results.
- `"0010" "011" "010" "Kimberling"`: one result, the unrelated partition paper
  `SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a350879-extreme-part-conditions/article.tex`,
  with a matched excerpt about A350879/A237753 extreme-part partition conditions.
  Its returned commit was `979b94ec4ec8a53194727e65b25d60ea7a930bd2`.

## Global code queries

- `"A289128" "conjecture"` returned our own already published Batch 10 files and
  OEIS-Spider copies of the original conjectures; no independent resolution.
- `"A289129" "limit"` and `"A289130" "limit"` returned our own result files and
  unrelated incidental hexadecimal matches; no predecessor proof or refutation.
- `"A289131" "recurrence"` returned our own result, the OEIS-Spider source copy,
  and joeis's `A289131.java`, which implements the *defined scalar recurrence*.
  That implementation does not prove equality with the original scanner lengths.
- `"Kimberling" "5/2" "5/3"` returned our own files and unrelated OEIS rational
  approximation/enumeration entries.

Our own results in this search were at commit
`2422f82913949a4f4a4db7c7616b09c43546aea7`. They were explicitly excluded as
evidence of independent priority. Queries returned at most 10 or 15 results;
GitHub indexing and exact text choices limit recall.

## Conclusion

No matching independent earlier resolution was identified in this additional
screen for the **one shared length assertion and two position-limit assertions**.
The newly discovered A211417 predecessor concerns a different number-theory
package and is outside this report. Do not turn the absence of a match here
into an unconditional novelty or priority claim.

Full request results are preserved only in the working research archive under
`research/batch11/sequences/`, as `batch10_proveit_extra_*.json` and
`batch10_global_extra_*.json`; they are not bundled with this published correction.
The exact query scopes, bounded findings, and relevant returned commits are
summarized above.
