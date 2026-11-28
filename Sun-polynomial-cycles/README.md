# Cyclic polynomial labels and OEIS A229827

In a circular ordering, each residue $x$ receives the label $P(x)+\sigma(x)$, where $\sigma(x)$ is its successor. Zhi-Wei Sun posed three existence assertions in September 2013. The first two manuscripts settle the three assertions in their stated form and classify the support of his counting sequence. The third settles the degree-two case over all odd finite fields. The fourth handles all mixed quadratics in characteristic two. [Original sequence and conjecture](https://oeis.org/A229827) · [Sun’s lecture, slide 36](https://www.mathnet.ru/PresentFiles/21090/sun.pdf)

| Question | Result | Manuscript |
|---|---|---|
| Can every prime field of order $p>3$ be ordered for $P=X^2$? | Yes. More generally, the orders on the integers modulo $n\ge 2$ exist exactly when $\gcd(n,6)=1$. | [Proof](square-circle.pdf) · [LaTeX](square-circle.tex) |
| Which odd fields admit an ordering for a quadratic of degree two? | Every such quadratic works over every odd field of order greater than three, including proper extensions in characteristic three. All fail over the field of order three. | [Odd-field proof](odd-fields.pdf) · [LaTeX](odd-fields.tex) |
| Which mixed quadratics work in characteristic two? | For $q=2^d$ and $ab\ne0$, every $aX^2+bX+c$ has at least $2^{2^{d-1}-1}$ directed orders up to rotation. More generally, every affine map with singular linear part on any finite vector space has at least $(k!)^{q/k}/k$ orders, where $k$ is the kernel size and $q$ the size of the space. | [Proof and counting argument](singular.pdf) · [LaTeX](singular.tex) |
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

A primitive multiplier ratio makes a triangular system of power-sum equations invertible through degree $q-3$. The new lemma proves the size of each nonempty proper component stays nonzero in the field, even when the field order is a higher power of its characteristic. For squaring the construction gives at least $(q+1)/2$ possible successors of zero and at least $\varphi(q-1)(q+1)/4$ directed circles up to rotation.

Lean 4.33.1 verifies the nonvanishing moment and the resulting nonzero component size from the triangular vanishing implication. The full circle construction is proved in the manuscript. The independent Python verifier constructs 2,457 cycles in 34 fields, examining 2,536 translations in total. It checks each cycle visits every element and each list of labels exhausts the field. Run `python3 -B verify_odd_fields.py`. [Lean lemmas](FieldMoments.lean) · [Verifier](verify_odd_fields.py) · [Output and nine-element example](odd-field-checks.txt)

The singular-affine verifier constructs and checks an order for every singular matrix over the binary spaces of dimensions two, three and four, and over the ternary plane. In the three smallest spaces it also independently counts all valid orders by going through every directed circle. The Lean file checks the switch of two successors and the final hyperplane avoidance step. Run `python3 verify_singular.py`. [Verifier](verify_singular.py) · [Counts](singular-checks.txt) · [Lean lemmas](SingularSwitch.lean)
