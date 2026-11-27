# Source and prior-work checks for A324017

Checked November 26, 2026 (America/Chicago).

## Primary statement

- [OEIS A324017](https://oeis.org/A324017).
- [Official data export](https://github.com/oeis/oeisdata/blob/main/seq/A324/A324017.seq).
- Header: `%I A324017 #91 Feb 16 2025 08:33:57`.
- Git blob: `a0e91a46abc07fe6c033b0dad19ac70f9c0afef6`.
- Snapshot: `source.seq`; SHA-256 in `SHA256SUMS.txt`.

The array definition uses a literal height-m integer power tower,
reduced modulo `(2n)^m`. The first comment quantifies over integers
`m,n,k>1`; the proved theorem includes that full domain. The second
comment requires `n>1,m≥2`; the exact formal quotient theorem has those
conditions. The third comment is false at `m=n=2,j=27`, even with the
additional canonical-residue restriction `0≤j<64`.

The third comment's example interchanges row and column indices relative
to the source's displayed table. This does not repair the quantified
claim refuted by the counterexample. The package explicitly distinguishes
the false literal claim from its proved weaker replacement.

## Classical primary sources inspected

1. Charles W. Trigg, Problem 559, *Crux Mathematicorum* **7** (1981),
   page 192. [June 1981 issue](https://cms.math.ca/wp-content/uploads/crux-pdfs/Crux_v7n06_Jun.pdf).
   Alan Wayne's discussion proposes a decimal expomorphic-number lifting
   rule. This is the reference linked from the OEIS entry.
2. Daniel B. Shapiro, solution to Problem 559, *Crux Mathematicorum*
   **13** (1987), pages 291–294.
   [November 1987 issue](https://cms.math.ca/wp-content/uploads/crux-pdfs/Crux_v13n09_Nov.pdf).
   This proves the earlier decimal lifting claim and discusses uniqueness.
   Its modulus base is ten; it is relevant prior work, not an unproved
   result introduced by the present package.
3. Daniel B. Shapiro and S. David Shapiro, *Iterated Exponents in Number
   Theory*, *Integers* **7** (2007), A23.
   [Author-hosted version](https://bpb-us-w2.wpmucdn.com/u.osu.edu/dist/c/5162/files/2018/02/IE-24ed9ge.pdf),
   [journal mirror](https://www.kurims.kyoto-u.ac.jp/EMIS/journals/INTEGERS/papers/h23/h23.pdf).
   The author's text was read, including the general stabilization result,
   fixed-point corollary, and lifting discussion. Those general ideas are
   classical and explicitly credited. The journal mirror did not open
   reliably; the author-hosted text was available.
4. J. Jiménez Urroz and J. Luis A. Yebra, *On the Equation a^x ≡ x
   (mod b^n)*, *Journal of Integer Sequences* **12** (2009), Article 09.8.8.
   [Primary paper](https://cs.uwaterloo.ca/journals/JIS/VOL12/Yebra/yebra4.pdf).
   Its theorem and Section 3 describe general exponential fixed-point
   lifting, including the sufficient period congruence used in this area.
   Its Section 3 example concerns odd b and exponential base `(b-1)^(b-1)`.
   The present even-b, exponential-base `b-1` proof is a specific elementary
   application of that established type of method.

## Bounded search

Both web search engines were used with exact-identifier and semantic
queries, including combinations of `A324017`, `Davis Smith`, `proof`,
`theorem`, `conjecture`, `counterexample`, `disproof`, `tetration`,
`2n-1`, and the displayed modular formulas. Checks included indexed
GitHub, trureturing, aiXiv, and Zenodo results. No earlier exact proof or
counterexample to these three comments was located.

The publication reports two proofs and one disproof of the three literal
OEIS assertions. It does not count auxiliary period or compatibility
lemmas as separate conjectures, assert global novelty of modular
tetration methods, or claim exhaustive publication priority.
