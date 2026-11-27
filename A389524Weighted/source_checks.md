# Source, dependency, and prior-work checks

Checked November 26, 2026 (America/Chicago). This is a bounded source and literature record; it does not certify exhaustive historical priority.

## Exact new assertion

[OEIS A389524](https://oeis.org/A389524), introduced by Mats Granvik on October 7, 2025, records three numbered conjectures. The earlier repository package proved Conjectures 1 and 3. This extension proves only the remaining **Conjecture 2** as a new assertion:

$$\sum_{k=1}^{n}T(n,n-k+1)(n-k+1)=A274628(n),\qquad n\ge1.$$

The target [A274628](https://oeis.org/A274628) is Nathanson's orphan-counting function. David Radcliffe's March 28, 2019 comment gives the literal interpretation: nonnegative integer solutions ab−cd=n with a>c and b>d. `Nathanson.Orphan` formalizes exactly these conditions. Its type has no artificial coordinate bound; the proof derives bounds and finiteness from the defining conditions.

## Preserved primary snapshots

The files below were read from the official `oeis/oeisdata` export and preserved with the earlier batch. The live public and internal A389524 pages were reopened for this extension and still display the same Conjecture 2 and its finite verification through n=500.

| Snapshot | OEIS revision | Git blob SHA |
|---|---|---|
| [A389524.seq](sources/A389524.seq) | 19, October 22, 2025 | `aada751ae99de30ed9ec5666012b6c7e06321bf5` |
| [A274628.seq](sources/A274628.seq) | 45, November 5, 2025 | `f0f507930335a96ce317d8720acd822966e40f5e` |

Primary URLs:

- https://oeis.org/A389524
- https://oeis.org/A389524/internal
- https://github.com/oeis/oeisdata/blob/main/seq/A389/A389524.seq
- https://oeis.org/A274628
- https://github.com/oeis/oeisdata/blob/main/seq/A274/A274628.seq

The source's reversed weighted row is proved verbatim as a finite sum in `A389524Weighted.original_conjecture`. The ordinary weighted order is separately stated as `weighted_row`. The triangle retains its integer codomain and original exceptional first column. Every positive index is covered.

## Classical ingredients and contribution boundary

The signed-partition identities are established mathematics. The complete three-page primary paper by Bressoud and Subbarao was read:

D. M. Bressoud and M. V. Subbarao, *On Uchimura's connection between partitions and the number of divisors*, Canadian Mathematical Bulletin 27 (1984), 143–145. https://doi.org/10.4153/CMB-1984-022-5 . Its equation (3) gives the generalized divisor identity with weight Σ_{j=1}^{s}(L−s+j)^r; its equation (8) records Uchimura's higher-moment framework. The 2018 online hosting date is distinct from the original journal publication in 1984.

The same ingredients appear explicitly in the author-submitted manuscript:

Archit Agarwal, Subhash Chand Bhoria, Pramod Eyyunni, and Bibekananda Maji, *Bressoud–Subbarao type weighted partition identities for a generalized divisor function*, arXiv:2210.03457, 2022. https://arxiv.org/pdf/2210.03457 . Equation (1.5) gives the generalized divisor weight. Equation (1.9) gives the second moment as the divisor convolution plus σ₁. The first four pages and relevant displayed formulas were inspected.

The earlier first-moment theorem is due to K. Uchimura, *An identity for the divisor generating function arising from sorting theory*, Journal of Combinatorial Theory, Series A 31 (1981), 131–135. https://doi.org/10.1016/0097-3165(81)90009-1 .

The orphan entry already records formulas in terms of divisor counts, divisor sums, and partitions. These are credited as prior mathematics. The present formal source derives the needed convolution relation using explicit bijections on the literal solution set, so it does not take an OEIS generating-function identity as a premise.

None of these classical references is presented as a new general identity. The contribution here is their complete connection to the particular recursively defined 2025 triangle, resolving its remaining numbered conjecture, together with a checked formal proof of the entire statement.

## Exact and semantic resolution searches

Both available web search engines were used. Queries included:

- `"A389524" "proof"`, `"A389524" "conjecture"`, and combinations with `proved`, `solved`, and `Lean`;
- `"A389524" "A274628"`, including queries excluding OEIS and sequence mirrors;
- `"A389524" "trureturing"` and `"A389524" "Low-Hanging Fruit"`;
- `"A274628" "weighted" sum`;
- combinations of `Uchimura`, `largest`, `smallest`, `partition`, and `orphan`.

The searches located the OEIS statement and the classical weighted-partition literature. They did not locate an earlier proof of the exact triangle-to-orphan connection.

An independent reviewer also reopened the live [trureturing public index](https://www.trureturing.org/conjectures). Its 2,235 listed results had no text match for A389524, A274628, orphan, or Uchimura. This is a check of the public index, not undisclosed work.

The reviewer reopened the primary abstracts and complete enumerated target lists of *Low-Hanging Fruit* I–V:

| Volume | Primary author-submitted abstract | Enumerated targets |
|---|---|---|
| I | https://aixiv.online/abs/2610.02669 | A000071, A038396, A237930, A055246 |
| II | https://aixiv.online/abs/2610.02670 | A000085 (odd-modulus claim), A028886 |
| III | https://aixiv.online/abs/2610.03153 | A153440, A266651, A007489, A114705 (weak claim), A000670, A000225 |
| IV | https://aixiv.online/abs/2611.00009 | A049803, A334511, A071307 |
| V | https://aixiv.online/abs/2611.00099 | A334513, A198632, A121320, A113249 |

Neither target is in those enumerations. This extension's check did not repeat a line-by-line audit of all five papers. An unchanged conjecture label and these bounded searches are insufficient to certify publication priority or editorial acceptance.

## Dependency provenance

The previous [A389524 package](../A389524/README.md) was published in commit `fb722daca887b23da66a55117a30e51838bcb105`. The extension is standalone: its four module sources and pinned build files are included locally.

| Dependency | Previous SHA-256 | Treatment here |
|---|---|---|
| `A389524/Uchimura.lean` | `878257266d1ebc4e4f1791dc18a3a2d9b7c6e0d323d4ecaecc8ecfe74423305a` | Copied byte-for-byte as `Uchimura.lean`. |
| `A389524/Proof.lean` | `54ebf0871d58e0f529d110dd2b641dab5f3f9d6370cb0455a3323616385d70ab` | Renamed `Triangle.lean`; its historical comment is clarified to say that the companion `Weighted.lean` now proves Conjecture 2. The theorem statements and proof terms are unchanged. |

`Orphans.lean` and `Weighted.lean` are the two new modules. The earlier Conjectures 1 and 3 are not counted as new results. The fresh package build and independent compilation cover all four exact delivered modules; `SHA256SUMS.txt` identifies their final contents.
