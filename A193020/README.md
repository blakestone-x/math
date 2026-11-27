# Distinct self-shuffles

For a word with run lengths $r_1,\ldots,r_h$, the number of distinct outputs from interleaving it with itself is at least the product of the adjacent binomial coefficients. Equality holds precisely for constant words and for factors of a periodic word with one run of each of two letters per period. This proves all nine of John W. Layman’s formulas at the offsets from −5 to +3 around powers of two. The common threshold is $k\ge4$.

The largest number of outputs from a length-$n$ binary word has exponential rate **4**. The paper gives a Catalan upper bound and a lower bound using the level sizes of ordered trees. More generally, interleaving $b$ copies over an alphabet of $q$ letters has maximum exponential rate $\min(b,q)^b$. The exact binary maximum at every length remains open.

Datko and Pawlik previously proved the singleton-letter formula and the lower bound for nonconstant binary roots. The trureturing collection records proofs of the +1 and −4 offsets. [Datko and Pawlik](https://doi.org/10.3390/sym17020305) · [trureturing dossier](https://the-omega-institute.github.io/trureturing-mdbook/Library/Digit/layman2011a193020.html) · [A193020](https://oeis.org/A193020) · [A331850](https://oeis.org/A331850)

[Manuscript](self-shuffles.pdf) · [LaTeX source](self-shuffles.tex) · [Exact verifier](verify.py)

Run `python3 verify.py` to enumerate all binary input words through length eight and all ternary input words through length six, and to check offsets, tree profiles and the rotating construction.
