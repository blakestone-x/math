# Permutations with prescribed occurrences of 1234 and 1243

Starting with a permutation and inserting each new minimum gives an exact enumeration by the number and type of the new pattern occurrences. For permutations avoiding 1234 and containing 1243 once, the calculation proves the four formulas proposed by Pedro Ferreira Pereira and Václav Kotešovec in November 2026. These are the radical generating function, two polynomial recurrences and the leading asymptotic. Brian Nakamura introduced the paired-pattern sequences in 2013. [A224292](https://oeis.org/A224292) · [Dated formula record](https://github.com/oeis/oeisdata/blob/976b0c73e00453b1c1e6f16d83108cb9bb744c3b/seq/A224/A224292.seq) · [Nakamura’s paper](https://arxiv.org/abs/1301.5080)

For **one occurrence of each** pattern, write $U=(1+x-\sqrt{1-6x+x^2})/(4x)$. The ordinary generating function is

$$
\frac{2(U-1)^6(2U-1)(U^2-U+1)}{U^3(2U^2-2U+1)}.
$$

The same derivation gives the series for two occurrences of either pattern while avoiding the other. The first mixed terms are $2x^6+32x^7+322x^8+2634x^9$. [A224293](https://oeis.org/A224293)

[Manuscript](one-pattern.pdf) · [LaTeX source](one-pattern.tex) · [Symbolic and direct verification](verify.py)

Run `python3 verify.py` with SymPy. It checks the differential identities for both recurrences, compares the series with 25 terms of each OEIS table, and counts the five pattern splits directly for every permutation through length nine.
