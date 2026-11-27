# Compositions and a divisibility theorem for OEIS A115047

Research notes for Blake Stone, November 26, 2026. Proofs developed with OpenAI Codex.

| Sequence | Result |
| --- | --- |
| A115047 | For every index n ≥ 3, n divides 12a(n). A positive universal multiplier works precisely when 12 divides it. The unique prime exception to the proposed divisibility by the index is 3. |
| A208354 | Two explicit weight-preserving bijections prove the single-run-of-ones conjecture, including the empty composition. |
| A323111 | If φ is the golden ratio, a(n) = (n+2)2^(n−3) − nφ^n/(5φ^5) + O(φ^n). This proves the proposed leading asymptotic and identifies the first exponentially smaller correction. |

The PDF contains the proofs for all indices. It uses Zograf's published recurrence and Alexandersson and Jordan's integrality theorem for A115047. The two composition arguments are self-contained.

## Files

- [OEIS-Compositions-and-Divisibility.pdf](OEIS-Compositions-and-Divisibility.pdf) is the four-page research note.
- [OEIS-Compositions-and-Divisibility.tex](OEIS-Compositions-and-Divisibility.tex) is its editable LaTeX source.
- [verify.py](verify.py) uses Python 3.8 or later and its standard library.
- [verification.txt](verification.txt) contains the output of the verifier.

Run the checks from the extracted directory.

    python3 verify.py

For A115047 the script checks every index from 3 to 120, evaluates the binomial identity at every admissible pair, and compares the recurrence with the independent Kaufmann–Manin–Zagier multinomial formula through index 15. For A208354 it compares the exact images of both bijections with an independently generated target set for each weight from 0 through 16. For A323111 it enumerates all compositions of 2n for 1 ≤ n ≤ 10, compares the counting formula with 32 tabulated terms, and evaluates the normalized error at three larger indices. All counts use integer or rational arithmetic. Only the displayed normalized errors use decimal arithmetic.

To rebuild the PDF with Tectonic, run the following in the extracted directory.

    tectonic OEIS-Compositions-and-Divisibility.tex

## Sources

- [OEIS A115047](https://oeis.org/A115047), including Michael Somos's 2014 prime-index conjecture.
- P. Alexandersson and L. Jordan, [Enumeration of Border-Strip Decompositions and Weil-Petersson Volumes](https://cs.uwaterloo.ca/journals/JIS/VOL22/Alexandersson/alex4.pdf), Journal of Integer Sequences 22 (2019), Article 19.4.5, Theorems 32 and 34 and Proposition 33.
- [OEIS A208354](https://oeis.org/A208354), including Gregory L. Simay's 2018 conjecture and Jerrold Grossman's 2024 observation.
- [OEIS A323111](https://oeis.org/A323111), including Václav Kotěšovec's 2019 asymptotic conjecture.
