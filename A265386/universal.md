# Universal growth and fluctuations within each parity

For arbitrary positive starting values in Sykora’s doubly Gray-transformed Fibonacci recurrence, the binary length eventually increases by one on alternate steps. Both the ordinary $n$th-root growth and the mean growth $(c_{2n}/c_n)^{1/n}$ tend to $\sqrt2$. [Manuscript](universal.pdf) · [LaTeX source](universal.tex)

The consecutive ratios on one parity eventually lie strictly between $0.5442$ and $0.6333$, and the other parity lies strictly between $3.1538$ and $3.7214$. Within **every four successive ratios of either parity**, three are pairwise more than $1/4096$ apart. Thus each parity has at least three accumulation points and the full ratio sequence has at least six, including for the original seed $(1,1)$.

The finite proof uses 99,771 recurrent prefix states at 19 bits. The verifier generates them in two coordinate systems, checks the alternating bit-length increases and the rational ratio extrema, and exhausts the four-ratio paths. Run `python3 universal_verify.py` with Python 3.9 or newer. [Exact verifier](universal_verify.py) · [Original-seed theorem](README.md) · [Source conjecture](https://oeis.org/A265386)
