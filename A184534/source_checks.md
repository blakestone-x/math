# Source and prior-work check: A184534

Checked November 27, 2026. This is a bounded, indexed search, not a certification of historical priority.

## Literal source and frozen export

The primary source is [OEIS A184534](https://oeis.org/A184534), revision 15 dated May 15, 2017. Clark Kimberling contributed the definition on January 16, 2011; Colin Barker contributed the empirical formulas on October 7, 2012. The source has offset 1 and defines the floor of the reciprocal fractional part of the positive real cube root of `n^3 + 4`.

The package retains [the exact export](sources/A184534.seq) from the [immutable OEIS-data commit](https://github.com/oeis/oeisdata/blob/571197984aeda7b8b680fe3a1f6a43f9898cd441/seq/A184/A184534.seq). That commit is the last file-touch commit returned by the repository history endpoint. A separate fetch of the pinned file was byte-compared to the current exported file and matched.

The target is Barker's empirical rational generating function. The source's separate empirical closed form is shifted by one: its value at n=3 is 12, whereas the literal root expression and the source data give 7. The package proves the generating function, supplies the correct all-index sequence, and exhibits this index discrepancy. Those are counted as one source-assertion resolution, with the discrepancy and general estimate supporting the result.

## Web searches

Both available web engines were used. Exact queries included `"A184534" proof`, `"A184534" proof formula`, `"A184534" proof cube`, and `"A184534" conjecture floor formula`. Semantic queries included `"fractional part" "cube root" "3n" floor reciprocal`, `"floor" "4+n^3" "proof"`, and `"reciprocal fractional" "cube" "floor"`.

The relevant results were the OEIS entry, its parent array [A184532](https://oeis.org/A184532), related fourth-root entries, and Sequence Machine's numerical fits. None supplied a proof of the selected assertion. Bruno Berselli's proofs for [A184536](https://oeis.org/A184536) and [A184537](https://oeis.org/A184537), dated January 30, 2011, already use elementary polynomial comparison for related fourth-root floors. The method of comparison is classical and is not claimed as a new technique here.

## Global GitHub search and inspected matches

The exact global query `A184534` found prior generators and program-synthesis artifacts. Relevant files were inspected:

| Prior item | What it contains | Relation to this package |
| --- | --- | --- |
| [jOEIS A184534](https://github.com/archmageirvine/joeis/blob/abb609413c9b320e769eaf41c0eef4ee43d1b5e7/src/irvine/oeis/a184/A184534.java) | A holonomic recurrence with initial values. | Existing computation of the same sequence; no real-root proof. |
| [LODA A184534](https://github.com/loda-lang/loda-programs/blob/f1b383b2344ab03ae8f79f41289360a6bd4394bd/oeis/184/A184534.asm) | An integer formula/program matching the initial data. | Prior formula, so no first-discovery claim for the expression. |
| [sequencelib A184534](https://github.com/provables/sequencelib/blob/dfb06c18bba196b5aa5bcb3725fe9d201fb9a61a/Sequencelib/Synthetic/A184/A184534.lean) | A synthesized integer-program definition with OEIS metadata. | A Lean definition alone; no fractional cube-root definition or theorem relating it to the source. |
| [OEIS ATP benchmark](https://github.com/ai4reason/oeis-atp-benchmark/blob/4a80a91728dffea1407ee2f0b8f55622761935cc/pb/A184534.smt2) | An unbounded equivalence benchmark for two synthesized integer programs (its assertion asks for a nonnegative index where they differ). | Neither integer program uses the real cube-root definition, so their equivalence does not prove the literal source bridge. |

Global semantic queries were also run, including `"cube root" "fractional" "reciprocal"`, `"Kimberling" "cube" "floor"`, `"fractional part" "cube root" "Kimberling"`, `"cube-root" "floor" "proof"`, and `"cubic" "reciprocal" "Kimberling"`. The inspected results concern numerical root libraries, unrelated cubic lattice sums, integer cube-root algorithms, or other OEIS conjectures. In particular, the [Atlas OEIS conjecture file](https://github.com/facebookresearch/atlas-lean/blob/a318749cc836cc17e83dfc0077419b3e80685558/WantedExt/NumberTheory/OeisConjecturesWanted.lean) concerns Sela Fried's different cube-root sum theorem. [Oudra's A248186 cubic-floor proof](https://github.com/the-omega-institute/trureturing/blob/720eb936a3bfd96a946ec055210f018951c4dfaa/Blueprint/D5/S3/ArithSums/OudraA248186CubicFloor.md) and the [Ma--Zhang paper](https://github.com/mathesis-papers/10.5281-zenodo.24410612/blob/021d6c1ad271a2d31c5478af7a8491df6dc18c46/manuscript/note.tex) solve a reciprocal-product-sum threshold, a different source definition and conclusion. Their full relevant statements were inspected. No target settlement was located.

## Scoped current-repository searches

Exact `A184534` searches were run in `VladimirReshetnikov/ProveIt` and `the-omega-institute/trureturing`. The sole combined hit was a coincidental hexadecimal substring in unrelated dynamics metadata. A separate ProveIt exact query returned no match.

Scoped semantic searches included `"reciprocal" "fractional" "cube"` and `"fractional" "cube" "floor"`. Observed indexed heads included ProveIt `55f050804e7225551f74934a0d678bc2a079a2cb` and trureturing `720eb936a3bfd96a946ec055210f018951c4dfaa`. The results concerned surreal numbers, the Fabius function, golden-ratio sequences, and foundational material; no proof of this source assertion was located. The later global search also observed ProveIt `62eec37178e9a0b7ea2306f09407541632d00df7` in an unrelated partition result. These are indexed snapshots, not a claim to have inspected every file of either repository.

## Conclusion and limits

The formula and recurrence predate this package as computational descriptions. The selected recorded generating-function assertion was still marked empirical in the current primary source; no earlier complete source-to-theorem proof was located in the bounded search. This package establishes that bridge and provides a kernel-checked proof. It does not claim that the elementary inequalities, the sequence formula, or global historical priority are new.

Query summaries and immutable result URLs are retained in [prior_search/search_summary.json](prior_search/search_summary.json) and [the final global semantic check](prior_search/semantic_global_summary.json). Third-party code and manuscripts are linked rather than redistributed.
