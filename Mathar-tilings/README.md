# A guide to all 44 conjectures in Mathar’s rectangular tiling paper

**Blake Stone · Proof developed with OpenAI Codex.**

Richard J. Mathar’s 2013 paper asks for generating functions for rectangular boards tiled by dominoes, longer straight bars, or $2\times3$ rectangles. Each coefficient counts tilings of one board. Some formulas identify tilings under symmetries, or restrict how many grid points have four tiles meeting, or how many horizontal lines cross the board without cutting any tile. The table links a derivation for every numbered conjecture in the original version. [Mathar, arXiv:1311.6135v1](https://arxiv.org/html/1311.6135v1)

| Conjecture | What the proof establishes |
|---|---|
| 1–2 | Both domino formulas follow by counting adjacent blocks in a two-letter word. [Bar tilings](../A232622/bar-crossings.md) |
| 3–4 | A transfer matrix gives both counts on three rows. In 3, the leading factor must be $2z^4$. Width four already gives six tilings with one four-tile meeting. Formula 4 holds as printed. [Three-row dominoes](../A232622/three-row-crossings.md) |
| 5 | Word reversal gives the domino symmetry count. [Bar tilings](../A232622/bar-crossings.md) |
| 6 | Shiqi Liu previously proved the three-row symmetry formula and its recurrence. [Proof and attribution](../A232622/README.md) |
| 7 | The three-row straight-tromino formula holds for every specified positive number of pairs of meetings. [Bar tilings](../A232622/bar-crossings.md) |
| 8–9 | A strip decomposition proves the junction-free count in 8. The formula in 9 counts the five-row board in Table 20, although equation (33) labels it as three rows. The unrestricted five-row result was already known. [Narrow strips](../Mathar-strips/README.md) |
| 10–12 | The word and its reversal give the three symmetry counts. In 12, the sign immediately before $1/(1-z-z^4)$ must be minus. [Bar tilings](../A232622/bar-crossings.md) |
| 13–14 | Counting adjacent blocks gives both four-row intersection formulas. [Bar tilings](../A232622/bar-crossings.md) |
| 15–18 | Formula 16 follows by counting junction-free five-row tilings with length-four bars. The unrestricted counts in 15, 17 and 18 follow from Mathar’s later calculations and from Aggarwal and Ram’s general theorem. [Narrow strips](../Mathar-strips/README.md) |
| 19–20 | Word reversal gives both four-row symmetry counts. [Bar tilings](../A232622/bar-crossings.md) |
| 21–22 | All six-row tilings by $2\times3$ rectangles have a two-letter encoding. Adjacent equal letters determine the meetings. [Six-row rectangles](../Mathar-hexominoes/README.md) |
| 23–24 | In 23 the numerator needs a positive $z^6$ term, as Mathar obtained in 2014. For 24, the first column forces one of four possible continuing patterns. [Eight-row rectangles](../Mathar-hexominoes/README.md) |
| 25–30 | A count of words up to the board symmetries gives the five-row total and all five specified meeting counts. [Five-row rectangles](../Mathar-hexominoes/README.md) |
| 31–34 | The symmetry formulas hold at all positive widths. In 31 the printed constant is two. Subtracting one counts the empty tiling once under Definition 8. [Six- and seven-row rectangles](../Mathar-hexominoes/README.md) |
| 35–39 | Marking horizontal slide lines and counting the independent strips they form proves all five fixed-board domino formulas. [Slide lines](slide-lines.md) |
| 40–41 | The same strip counts, with word reversal on the two-row strip, prove both three-row symmetry formulas. [Slide lines](slide-lines.md) |
| 42–44 | Splitting along marked lines and counting the remaining one-, two- and three-row strips proves the three straight-tromino formulas. [Slide lines](slide-lines.md) |

## Earlier results and checks

Mathar’s original paper supplies several of the block and strip interpretations. His 2014 transfer-matrix paper gives the unrestricted formulas underlying 9, 15, 17 and 18 and the corrected numerator for 23. Aggarwal and Ram later proved the general unrestricted narrow-strip formula. Liu’s proof of 6 predates the exposition here. The linked notes give more specific sources where the arguments use earlier work. The 44 numbers index statements in the 2013 paper. Several are consequences of the same counting argument. [Mathar, 2014](https://arxiv.org/abs/1406.7788) · [Aggarwal and Ram, 2023](https://cs.uwaterloo.ca/journals/JIS/VOL26/Ram/ram3.pdf) · [Liu’s preprint](https://github.com/Lshiqi67/domino-tilings-a232622/releases/tag/paper-en-v2.1)

The companion programs check the rational identities for the bar and slide-line formulas, enumerate small narrow strips independently, and certify the two eight-row hexomino generating functions through a finite transfer matrix. The notes specify which checks are identities for all widths and which are finite enumerations. [Bar identities](../A232622/verify.py) · [Narrow-strip enumerator](../Mathar-strips/verify.py) · [Hexomino certificate](../Mathar-hexominoes/verify.py) · [Slide-line identities](verify-slide-lines.py)
