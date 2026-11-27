# The positions of minimum parts in compositions

Blake Stone · Proof developed with OpenAI Codex.

For an ordered composition, count the position of each occurrence of its smallest part. The total over all compositions of n is asymptotic to n²·2^(n−5), as conjectured by Václav Kotešovec. For n at least two, the contribution from compositions containing a one is exactly (n+1)(n+6)·2^(n−5). The remaining contributions are exponentially smaller.

[One-page manuscript](minimum-positions.pdf) · [LaTeX source](minimum-positions.tex) · [Direct enumeration](verify.py) · [OEIS A377824](https://oeis.org/A377824)
