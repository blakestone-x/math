# Digit-sum residues on arithmetic progressions in every rational base

Cassaigne, Espinoza, Rigo and Stipulanti asked whether the sum of the digits in base $3/2$ is equally distributed modulo every $m$. This manuscript proves that every residue has frequency $1/m$, even when the inputs are restricted to an arbitrary arithmetic progression. It also gives the exact distribution for every reduced rational base $p/q>1$. [Original question, Section 4](https://arxiv.org/html/2602.21895v1) · [Manuscript (PDF)](digit-sums.pdf) · [LaTeX source](digit-sums.tex)

Write $S(n)$ for the sum of the canonical rational-base digits. At one division step, the next digit is the remainder of $qn$ modulo $p$, and the next input is the quotient. Fix a step $A\ge1$, a modulus $m\ge2$, and an offset $b\ge0$. Put $g=\gcd(m,A,p-q)$. At the inputs $Aj+b$, residue $c$ has limiting frequency $g/m$ if $c\equiv qb\pmod g$, and zero otherwise. The error tends to zero uniformly in the offset $b$.

| Base | Inputs | Modulus | Limiting frequencies |
| --- | --- | --- | --- |
| $3/2$ | $6j+7$ | $5$ | All five residues have frequency $1/5$. |
| $5/2$ | $6j+1$ | $6$ | Residues $2$ and $5$ each have frequency $1/2$. |
| $7/3$ | $6j+1$ | $8$ | Each odd residue has frequency $1/4$. |
| $10$ | $9j+7$ | $9$ | Residue $7$ has frequency $1$. |

The proof finds a residue class on which adding one creates a carry at exactly one of two positions. At sufficiently large digit depth this supplies a positive proportion of pairs with identical higher digits and different lower digit sums modulo the order of the character being averaged. The resulting cancellation leaves exactly the characters responsible for the congruence modulo $g$.

## Formal proof

[Distribution.lean](Distribution.lean) proves `uniform_residue_frequencies` for arbitrary coprime $p>q\ge1$, every positive modulus and step, and an arbitrary offset function $b(N)$. The latter quantifier allows the starting point to change with the length of the sample. The named specialization `three_halves_all_moduli` gives the $1/m$ limit.

- [Digits.lean](Digits.lean) defines the digit sum and proves the carry witness and the congruence modulo $p-q$.
- [Cancellation.lean](Cancellation.lean) proves the lower bound on the number of residue classes with a common higher-digit part and different phases.
- [Averages.lean](Averages.lean) proves contraction for steps coprime to $p$. [Progressions.lean](Progressions.lean) handles all steps and identifies the surviving characters.
- [DekkingBridge.lean](DekkingBridge.lean) identifies digit-sum parity with the normalized binary word in the [earlier manuscript](../Dekking-base-three-halves/README.md). It proves `unconditional_factor_frequencies` for both binary words, including the reversal and complement symmetries on all dyadic progressions, directly from the sequence definitions.

## Reproducing the checks

Run these commands from this directory in a checkout of the repository. The formal connection to the binary words uses the adjacent Dekking project. The independent Python verifier checks place-value reconstructions, carry witnesses, exact cancellation counts and sample residue distributions. [Verifier](verify.py) · [Verification output](verification.txt)

```sh
lake exe cache get
lake build
python3 verify.py
sha256sum -c SHA256SUMS
```
