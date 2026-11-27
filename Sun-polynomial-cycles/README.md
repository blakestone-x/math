# Cyclic polynomial labels and OEIS A229827

In a circular ordering, each residue $x$ receives the label $P(x)+\sigma(x)$, where $\sigma(x)$ is its successor. Zhi-Wei Sun posed three existence assertions in September 2013. Two manuscripts settle them and classify the support of his counting sequence. [Original sequence and conjecture](https://oeis.org/A229827) · [Sun’s lecture, slide 36](https://www.mathnet.ru/PresentFiles/21090/sun.pdf)

| Question | Result | Manuscript |
|---|---|---|
| Can every prime field of order $p>3$ be ordered for $P=X^2$? | Yes. More generally, the orders on the integers modulo $n\ge 2$ exist exactly when $\gcd(n,6)=1$. | [Proof](square-circle.pdf) · [LaTeX](square-circle.tex) |
| Does every finite field of order $q$ have an order for every $P\ne c-X$ of degree less than $q-1$? | Squaring on the field of eight elements gives a counterexample. | [Proof](manuscript.pdf) · [LaTeX](manuscript.tex) |
| Does every eligible finite subset of a field of order greater than seven have such an order? | Squaring on $\{-5/4,1/4,7/4\}\subset\mathbb Q$ forces equal labels in both circular orientations. | [Proof](manuscript.pdf) · [Lean certificate](ThreePoint.lean) |

The positive construction joins permutation cycles by exchanging the successors of $x$ and $-x$. A polynomial in the translation parameter bounds how many translations can fail to join all cycles. A digit construction and the Chinese remainder theorem give every composite case. Counting the construction gives

$$
 \mathrm{A229827}(p)\ge\frac{(p^2-1)(p-3)}{16},
 \qquad \mathrm{A229827}(p^{e+1})\ge(p-1)p^{p^e-1}\mathrm{A229827}(p^e)
$$

for each prime $p>3$ and $e\ge 1$. The same existence theorem holds for all quadratics $aX^2+bX+c$ with invertible $a$ on those residue rings.

The second manuscript gives a hand proof of both obstructions and classifies every polynomial function of degree less than $q-1$ for $q\le8$. At $q=4,8$, its exceptions are exactly the even permutations of the field. At $q=3,5,7$ they are exactly the functions $c-X$. Under the degree condition only constants occur at $q=2$, and each works.

## Verification

- `python3 -B verify_prime_cycles.py` checks every modulus $2\le n\le3000$, every quadratic edge of the 999 admissible cases, and the moment obstruction for all 8,650 multiplier-pair and translation choices at primes from 5 through 31. It also independently enumerates every circle for $n\le9$. [Python verifier](verify_prime_cycles.py) · [Recorded output](prime-verification.txt)
- `c++ -O2 -std=c++17 verify.cpp -o /tmp/sun-polynomial-verify && /tmp/sun-polynomial-verify` enumerates every normalized polynomial function and every possible circular ordering through $q=8$. [C++ verifier](verify.cpp) · [Recorded output](verification.txt)
- Lean 4.19 with mathlib verifies injectivity of the displayed rational triple and the necessary collision in every cyclic ordering of its members. Run `lake env lean /absolute/path/to/ThreePoint.lean` in a mathlib 4.19 project. The general constructive proof is in the first manuscript. [Lean source](ThreePoint.lean)

- A second Lean 4.19 file proves $\gcd(n,6)=1$ for every $n\ge2$ and every permutation $\sigma$ of $\mathbb Z/n\mathbb Z$ for which $x\mapsto x^2+\sigma(x)$ is bijective. The proof passes through divisibility of the integer sum of squares. It also constructs the two prime-field multipliers with opposite Euler-criterion powers for every prime $p>3$. Run `lake env lean /absolute/path/to/Necessity.lean`. Both theorems report only `propext`, `Classical.choice`, and `Quot.sound`. [Lean necessity and prime multiplier proofs](Necessity.lean)
