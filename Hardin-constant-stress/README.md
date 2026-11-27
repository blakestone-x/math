# When do rectangle counts obey a common recurrence?

Research manuscript for Blake Stone, prepared with OpenAI Codex. [Paper (PDF)](rectangular-recurrences.pdf) · [LaTeX](rectangular-recurrences.tex) · [Exact recurrence coefficients](catalog.json)

R. H. Hardin conjectured that particular rectangular array counts satisfy the same recurrence at every width and height. The paper proves **25 table-level recurrence predictions**. Five constant-stress cases have earlier proofs, credited below. The other 20 comprise 17 constant-stress tables, two median tables and one six-difference table. Three further constant-stress tables receive exact least orders. Independent mathematical review is pending.

## The threshold for a common recurrence

Color a rectangle with integers from $0$ through $q-1$. In each adjacent square require the two diagonal sums to differ by $d>0$ in absolute value. A common recurrence uses the same coefficients at every positive width.

- For ordinary arrays a common linear recurrence exists **exactly when $q\le 2d$**.
- In the tilted version, orthogonal neighbors must differ. The same threshold holds with two extra cases at stress one. Three colors give no arrays, and four colors give exactly eight at every positive size.
- With $q\le d\le 2q-2$, the paper gives an explicit product for the least common polynomial. A rectangle just three columns wide already needs its full degree.

For example, with eight colors the tilted model has no common recurrence at stress three. It has one at stress four. The least orders at stresses five, six and seven are 82, 61 and 58. [Hardin's order-61 prediction](https://oeis.org/A235248) · [Order-58 prediction](https://oeis.org/A235258)

The proof reconstructs each cell from its boundary phases modulo $2d$. For an arbitrary fixed width, the feasible choices for all later rows form a bipartite graph on at most $2q$ vertices. A sum of squares identifies the least polynomial that works simultaneously for every reachable graph. Above the threshold, independently filling the sites in even rows and even columns gives exponential growth rates that increase without bound with the width.

## Constant-stress results

The entries in each row are in the same order as their least recurrence degrees. The full signed coefficients and source-column witnesses are in the catalog.

| Results | OEIS tables | Least degrees |
|---|---|---|
| Ordinary all-width predictions | [A234227](https://oeis.org/A234227), [A234266](https://oeis.org/A234266), [A234564](https://oeis.org/A234564), [A234681](https://oeis.org/A234681), [A234690](https://oeis.org/A234690), [A234712](https://oeis.org/A234712), [A234728](https://oeis.org/A234728), [A234738](https://oeis.org/A234738), [A234823](https://oeis.org/A234823) | 16, 6, 14, 18, 29, 36, 30, 23, 23 |
| Tilted all-width predictions | [A235017](https://oeis.org/A235017), [A235087](https://oeis.org/A235087), [A235098](https://oeis.org/A235098), [A235186](https://oeis.org/A235186), [A235198](https://oeis.org/A235198), [A235239](https://oeis.org/A235239), [A235248](https://oeis.org/A235248), [A235258](https://oeis.org/A235258) | 10, 16, 23, 27, 39, 41, 61, 58 |
| All-width predictions with earlier proofs | [A235280](https://oeis.org/A235280), [A235289](https://oeis.org/A235289), [A235301](https://oeis.org/A235301), [A235310](https://oeis.org/A235310), [A235319](https://oeis.org/A235319) | 9, 6, 10, 14, 18 |
| Further exact orders for tables with published strip data | [A234658](https://oeis.org/A234658), [A234702](https://oeis.org/A234702), [A235212](https://oeis.org/A235212) | 23, 39, 82 |

## Two other local rules

For an ordered alphabet of $q$ colors, if the minimum plus the upper median equals the lower median plus the maximum on every square, the exact number of $(n+1)\times(k+1)$ arrays is

$$q^{n+1}+q^{k+1}-q+q(q-1)(2^n-1)(2^k-1).$$

Every square uses each of its colors an even number of times. This determines the entire rectangle from the colors on its first row and column. The formula proves both all-width predictions, both diagonal recurrences and Colin Barker's 14 column generating functions and closed forms. [A235884](https://oeis.org/A235884) · [A235893](https://oeis.org/A235893)

For the four-color rule requiring the six pairwise absolute differences in each square to sum to nine, the least common polynomial is $(X-1)(X-2)(X^2-2)(X^2-8)$. Every square contains one 0, one 3 and a pair of equal colors, counted with multiplicity. [A234140](https://oeis.org/A234140)

## Verification and sources

The two Python verifiers check every reachable graph in the 25 stress cases, the three parity-rule tables and small rectangles counted directly from their original definitions. The optional source audit matches **175 fixed-column or diagonal recurrences, 67 rational generating functions and 15 closed forms**. These are consequences of the table theorems. The Lean 4.19 proof establishes that all finite rectangles in the threshold range are uniquely determined by their first row and column. [Stress verifier](verify.py) · [Parity verifier](parity.py) · [Source audit](check_sources.py) · [Lean boundary theorem](Boundary.lean)

Run the numerical and algebraic checks with Python 3.10+ and SymPy. The paper builds with Tectonic.

```sh
python verify.py
python parity.py
lean Boundary.lean
tectonic rectangular-recurrences.tex
```

To run the source audit, check out the OEIS revision below with the directories `seq/A234` and `seq/A235` available. Fetch the six supporting text files listed in the catalog using Git LFS, or place them together and pass their directory as `--attachments`. The script verifies each attachment's SHA-256 digest.

```sh
python check_sources.py /path/to/oeisdata
```

The original predictions and numerical source data are due to R. H. Hardin, Colin Barker and the OEIS Foundation. The original data are licensed under CC BY-SA 4.0. The Omega Institute previously proved the five all-width predictions identified above, used a boundary-word method modulo six for A235301, and proved the general fixed-deficit alphabet equivalence. [Pinned OEIS export](https://github.com/oeis/oeisdata/tree/976b0c73e00453b1c1e6f16d83108cb9bb744c3b) · [OEIS data license](https://creativecommons.org/licenses/by-sa/4.0/) · [Prior problem statements](https://github.com/the-omega-institute/trureturing/tree/9ccf7e999d9d317777dacc48da28169af2c994e6/Problems) · [Prior fixed-deficit theorem](https://github.com/the-omega-institute/trureturing/blob/9ccf7e999d9d317777dacc48da28169af2c994e6/D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235280A235310Alphabet.lean)
