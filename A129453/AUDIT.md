# Independent mathematical and Lean audit

Reviewed November 26, 2026, by a separate proof-audit agent.

## Result

The full integer-square refinement is established for every pair of natural
numbers `n,k` satisfying `k ≤ n`, including `n = k = 0` and both boundary
columns. The final packaged source was read and independently recompiled;
compilation exited with status 0. All three printed theorem dependencies
are exactly `propext`, `Classical.choice`, and `Quot.sound`.

Audited source SHA256:

```text
7ebdcf093cf3fdd6bc85455b24629e6797b50a4b61f2543f3fdd9421b46301a3  Proof.lean
```

The independent command and its complete output are recorded in
`audit-verification.txt`.

## Match to the original OEIS sequence

The official [A129453 internal entry](https://oeis.org/A129453/internal),
revision 9 dated February 7, 2024, was independently retrieved. It defines
the triangle from the double gcd product and separately suggests ordinary
integrality, divisibility by the corresponding binomial coefficient, and
an integer-square quotient.

The formal definition

```lean
def gcdProduct (n : ℕ) : ℕ :=
  ∏ i ∈ range n, ∏ j ∈ range n, Nat.gcd (i+1) (j+1)
```

is exactly the product over `1 ≤ i,j ≤ n`. At `n = 0` it is the empty
product 1, as required by the entry. The proof does not replace this
definition by a conjectured factorization: it derives the valuation of
the original double product by counting multiples of each prime power.

## Mathematical check

For a prime `p`, the proof establishes

$$
v_p(G(n))=\sum_{r\ge1}\left\lfloor n/p^r\right\rfloor^2.
$$

It also derives the usual factorial valuation formula and uses the exact
factorial identity for binomial coefficients. For each prime-power
denominator, set

$$
x=\lfloor n/p^r\rfloor,\quad
y=\lfloor k/p^r\rfloor,\quad
z=\lfloor(n-k)/p^r\rfloor.
$$

Because `k ≤ n`, one has `x = y+z+c` with `c` equal to 0 or 1. The local
exponent calculation is

$$
x^2-y^2-z^2-c=2\bigl(yz+c(y+z)\bigr).
$$

The right side is an even nonnegative integer. Summing it proves both
nonnegativity and evenness of every prime exponent remaining after
division by `choose(n,k) G(k) G(n-k)`.

All sums in Lean have finite, justified bounds. `factorization_as_sum`
uses the factorization bound to show that the selected prime-power
divisors are exactly the required finite range. Thus no informal infinite
sum, unchecked truncation, or finite experimental prefix is used to
establish the universal theorem.

## Denominators and exact division

Every gcd factor has positive inputs, so `gcdProduct n ≠ 0` is proved for
all `n`. The hypothesis `k ≤ n` gives `choose(n,k) > 0`. Their product is
therefore nonzero, allowing the factorization comparison to imply actual
divisibility. After obtaining a positive quotient, the proof constructs
an integer square root from its even prime exponents.

The central statement is stronger than a formula involving natural-number
division:

```lean
∃ t : ℕ, gcdProduct n =
  n.choose k * gcdProduct k * gcdProduct (n-k) * t^2
```

This exact equality, together with the proved nonzero denominators, rules
out any possibility that truncated natural division conceals a failure
of rational integrality. The later `triangle`, `binomial_dvd`, and
`quotient_square` theorems follow by exact division. They consequently
describe the original rational triangle as well.

## Prior work and scope

Wanli Ma's [2025 paper, *Generalized factorials characterized by Dirichlet
convolution*](https://arxiv.org/abs/2509.13354), was independently checked.
Equation (2.3) identifies this double gcd product; the surrounding
argument and Theorem 2.5 give its ordinary generalized-binomial
integrality. That ordinary-integrality conclusion is prior work and is
not the new claim being attributed to this package.

The selected assertion is the stronger one: division by the ordinary
binomial coefficient leaves an **integer square**. The formal theorem
establishes that stronger statement directly. This audit verifies the
mathematics, formal source, index domain, and match to the stated source;
it does not certify exhaustive historical priority. The package README
records the broader literature-search scope and its limitations.

No placeholder, added axiom, `native_decide`, circular definition,
unproved hypothesis equivalent to the conclusion, or missing boundary
case was found.
