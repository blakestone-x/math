# Source and prior-work dossier: A067576

Checked November 27, 2026. This is a bounded public-source search, not a claim to have established global historical priority.

## Exact source and assertion

The primary record is [OEIS A067576](https://oeis.org/A067576), revision 57, November 11, 2025 at 21:29:38. Its array definition is the increasing list of positive integers of each fixed binary weight. Kimberling's November 8, 2025 comment conjectures eventual ratio-two growth after adding one to each entry. His five reported starting rows are 1,1,2,3,4.

The frozen [source export](sources/A067576.seq) was fetched independently at [OEIS-data commit eb3c646fa1194774d4a21422a028616eaf549691](https://github.com/oeis/oeisdata/blob/eb3c646fa1194774d4a21422a028616eaf549691/seq/A067/A067576.seq), the last file-touch commit returned by repository history. The current/default export and pinned export matched. The saved file is exactly the 2,333-byte fetched pinned content, with SHA256 `5fc8472d8dc9c5b2afe7e374bc5261150bf3d5cdaff75d0effe24746268ee8ab`.

The source uses i,j≥1. Its prose about d(k) is read as the starting row index; the printed values make this clear (the second column never contains the number 1, yet d(2)=1). The theorem defines onset explicitly as the least positive r such that all transitions i≥r double. We prove this exact property, with r=max(1,j−1), and do not depend on that prose shorthand.

`entry i j` is defined by `Nat.nth (fun n => n.bitIndices.length = i) (j-1)`. The package proves that every positive-weight row is infinite, positive, strictly increasing, and has the correct rank. Thus the theorem refers to the source array, not a recursively defined replacement. The auxiliary row i=0 is an internal base case; the public mathematical claim uses positive rows and columns. The antidiagonal orientation is checked against all 66 displayed source terms.

## Relevant prior statements and methods

| Primary source inspected | What it establishes or contains | Relation to this proof |
| --- | --- | --- |
| [open-math-agents statement at current observed commit 3a0039b](https://github.com/GuillaumeBAUD-coder/open-math-agents/blob/3a0039bdf1da87d3915b73dabafd68415871f2e4/statements/oeis-a067576.lean) | The same literal `Nat.nth` definition and exact `IsLeast` onset assertion, indexed as column j+1 with onset max(1,j). The proof consists of `sorry`. | The strengthened onset was already formulated. This is an admitted statement, not an existing proof. Our package does not claim first formulation. The complete file was fetched at the initial global-hit commit and again at this current observed commit. |
| [jOEIS A067576.java](https://github.com/archmageirvine/joeis/blob/abb609413c9b320e769eaf41c0eef4ee43d1b5e7/src/irvine/oeis/a067/A067576.java) | Generates rows by fixed-popcount successor (`SWIZZLE`), interleaving the antidiagonals. | Complete implementation inspected. It generates the source sequence but gives no proof of eventual doubling or the exact onset. |
| [A036563](https://oeis.org/A036563), revision 132, February 9, 2026 | The formula 2^n−3; Zumkeller's March 6, 2003 comment identifies its shifted terms with the nth integer having n binary ones. | Prior diagonal special case T(n,n)=2^{n+1}−3, credited. The package does not claim the first discovery of every special case of the closed form. |
| [A066884](https://oeis.org/A066884), revision 51, September 19, 2025 | The same array read in the reverse antidiagonal direction; identifies first columns A000225 and A055010 and known diagonals. Links the following paper. | Establishes classical array context and earlier special cases. No eventual-column assertion appears in this inspected record. |
| [Vladimir Dobrić, Marina Skyers and Lee J. Stanley, arXiv:1603.04896v1](https://arxiv.org/pdf/1603.04896), submitted March 15, 2016 | Section 3.4 gives weight ranking/unranking algorithms, an exact binomial count (Lemma 3, attributed to S. Buss), and a polynomial-time consequence for A066884. Remark 2 gives minimum/maximum fixed-weight words. | The relevant ranking section and surrounding statement were inspected in the primary PDF. The paper develops the general classical framework; we found no stated eventual-doubling or sharp-onset theorem there. Our elementary count proof does not claim a new binary ranking method. |

## Exact and semantic search scope

The compact machine-readable record is [prior_search/search_summary.json](prior_search/search_summary.json). Searches were run before investing in the final package and included semantic terms rather than relying solely on the sequence identifier.

**GitHub exact queries.** A global `A067576` query returned 25 visible hits, including the sources described above, the inverse-sequence generator A356419, Math-PlanePath tests, a lexicographic binary implementation, candidate catalogues, and incidental hexadecimal/text matches. An exact query in the current open-math-agents repository returned only the admitted statement. A combined exact query in `VladimirReshetnikov/ProveIt` and `the-omega-institute/trureturing` returned no hits.

**GitHub semantic queries.** Global queries covered binary/eventual-geometric/column, popcount/column/geometric, binary-expansion/doubling/Kimberling, set-bits/doubling/column, and bitIndices/column. The returned pages were screened for a theorem covering eventual growth of fixed-rank binary-weight columns. The only matching formal target found was the admitted open-math-agents statement. Other matches concerned software, unrelated combinatorics, or general binary techniques. Scoped current-repository queries covered popcount/doubling and binary/eventually-geometric. Observed scoped revisions were ProveIt `49af140e6ff2b0d19fa62ff703ccfc0cc25b3e68` and trureturing `720eb936a3bfd96a946ec055210f018951c4dfaa`; the semantic matches concerned unrelated binary encodings and combinatorial projects, with no target proof located.

**Both web engines.** Queries included `"A067576" proof conjecture`, `"A067576" proof`, `"Kimberling" "binary" "doubling"`, `"binary" "eventually geometric" "Kimberling"`, `"popcount" "columns" "eventually" geometric`, and `"binary expansion" "column" "geometric" "A067576"`. An additional primary-paper-title search led to the related 2016 paper, which was opened and inspected. Searches returned the OEIS target and related entries, the ranking paper, and unrelated binary/phi/Fibonacci material; no proof of this exact column assertion was located.

The supplied package therefore resolves one explicitly recorded conjecture under the source's literal definition. Its exact formula and minimal onset are proved components of the same source family. The bounded searches do not establish first-ever discovery or rule out uncatalogued prior work.

## Verification

The fresh [author build](verification.txt) compiled all four explicit local roots successfully. Each principal axiom report uses only `propext`, `Classical.choice`, and `Quot.sound`. The finite [integer replay](verification_python.json) checks the source prefix, 3,319 formula values, 3,239 doubling equations, and 78 preceding-row failures; the complete unbounded proofs are in the Lean modules.
