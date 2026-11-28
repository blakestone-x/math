# Supercongruences for Peter Bala's companion binomial sums

Peter Bala conjectured in 2023 that two integer-parameter families, $u_m$ and $v_m$, satisfy the same prime-power congruence as the Franel numbers. This paper proves the $v_m$ half for every integer $m$. Wentao Li had already proved the $u_m$ half in Lean. Together the results cover both families in A363985. [Bala’s conjecture](https://oeis.org/A363985) · [Li’s earlier proof](https://github.com/VictorLiwentao/fc-palomar-proofs/tree/2329f9d4bebb30be1bb59e40476a89b44d6e034c/FCPalomar/OeisA363985) · [Manuscript](companion.pdf) · [Editable LaTeX](companion.tex)

$$
v_m(N)=\sum_{k=0}^{N}(-4)^{N-k}\binom Nk\binom{mN+2k}{2k}\binom{2k}{k}.
$$

For every prime $p\ge5$ and $n,r\ge1$, the difference $v_m(np^r)-v_m(np^{r-1})$ is divisible by $p^{3r}$. At $p=3$ the paper proves divisibility by $3^{3r-1}$. For $m=2$ the difference at $n=r=1$ is $5984-8=5976$, which is divisible by 9 and leaves remainder 9 modulo 27.

| Source | Result | Left to Solve statement review |
|---|---|---|
| [A363985](https://oeis.org/A363985) | Both families for all integer parameters, combining Li’s $u_m$ theorem with this $v_m$ theorem | [#22389](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/22389) |
| [A363986](https://oeis.org/A363986) | $v_2$ for every prime and exponent in the conjecture | [#22398](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/22398) |
| [A363988](https://oeis.org/A363988) | $v_3$ for every prime and exponent in the conjecture | [#22395](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/22395) |
| [A363990](https://oeis.org/A363990) | $v_4$ for every prime and exponent in the conjecture | [#22400](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/22400) |

A coefficient transformation proves the result for a wider class of signed convolutions. The proof pairs the triples divisible by $p$ with the terms at the preceding scale. For the two unit indices left over, a sum of inverse squares over complete residue blocks supplies the missing factor. The manuscript uses the integer-top Jacobsthal congruence in [Straub’s Lemma 5.1](https://doi.org/10.2140/ant.2014.8.1985).

## Verification

The standard-library Python script performs 1,173 exact transformation checks, 312 prime-power comparisons on the original sums, and 256 checks of the broader convolution across all eight sign choices. It also compares five values from each named OEIS entry. Run `python3 -B verify.py`. [Verifier](verify.py) · [Expected output](verification.txt)

Lean proves the inverse-square cancellation over the units of any commutative ring with finitely many units in which 2 and 3 are invertible. It also proves that multiplying the sum by 3 kills it whenever 2 is a unit. The full supercongruence proof is in the manuscript. The four proposed board statements compiled under Lean 4.33.1 at formal-conjectures commit `9097e2f90e66d2f6244209cb1c07f7120d17ec53`. [Lean cancellation proof](UnitSquares.lean) · [Submitted statements](OMAStatements)
