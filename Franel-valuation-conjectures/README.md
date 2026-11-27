# Three conjectures on Franel recurrences and binomial power sums

In their 2014 MSRI-UP report, Abraham Schulte, Samantha VanSchalkwyk and Adela Yang asked which initial values give an integral Franel recurrence, when an entire binomial power-sum sequence avoids a prime, and when half a binomial power sum is odd. This paper proves their Conjectures 4.5, 5.4 and 5.6. [Original report, pp. 158–160](https://slmath-production-assets.sfo3.digitaloceanspaces.com/system/cms/files/81/files/original/Research_Reports_2014_MSRI-UP_%28Single_File%29.pdf) · [Proof manuscript](manuscript.pdf) · [Editable source](manuscript.tex)

| Question | Result |
|---|---|
| Integral initial values | All terms are integers exactly when $u_1=2u_0$. Otherwise reduced denominators have unbounded powers of every odd prime. The paper also gives exact valuations at the first affected prime index and on powers of three. |
| Avoided primes | Some prime divides none of the binomial power sums exactly when the exponent is odd. Three is always a witness in that case. For even exponents every prime $p$ divides the term at $n=p-1$, also a special case of Calkin’s earlier interval theorem. |
| Binomial power sums | For every integer exponent $a\ge2$ and every positive row index $n$, half the sum of $\binom nk^a$ is odd exactly when $n$ is a power of two. |
| Sharp extension | The largest uniform modulus $2^h$ under which the sum equals the number of odd binomial coefficients has $h=2$ for odd $a$ and $h=\min(a,3+v_2(a))$ for even $a$. Rows two and three witness sharpness. |

The proofs use a determinant identity, Lucas’s theorem and congruences of paired binomial coefficients. The standard-library Python program independently checks the determinant recurrence against literal binomial sums, exact denominators, and the uniform modulus. Run `python3 -B verify.py`. [Verifier](verify.py) · [Recorded output](verification.txt)

A Lean 4.19.0 formalization checks the determinant identity and the integer-initial-value classification. Given the classical integer Franel solution with initial values $(1,2)$, the theorem `FranelIntegral.integral_solutions_iff` shows that an integer solution with initial values $(a,b)$ exists exactly when $b=2a$. The finite sums and their classical recurrence supply that input in the manuscript. Run `lake env lean /absolute/path/to/IntegralInitials.lean` in a Mathlib checkout at commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. [Lean source](IntegralInitials.lean)
