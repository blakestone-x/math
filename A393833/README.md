# A393833: existence of palindromic proper-divisor residue lists

**Blake Stone** · Proof developed with OpenAI Astra 6.2 · November 26, 2026

## Result

[OEIS A393833](https://oeis.org/A393833), proposed by Michel Lagneau on
March 1, 2026, asks for the least positive integer with exactly $2n+2$
divisors whose $2n+1$ proper divisors, in increasing order and reduced
modulo $n$, form a palindrome. Its recorded conjecture asserts that a
witness exists for every $n\ge1$.

We prove that conjecture, including the divisor-count requirement in the
sequence definition. In fact, witnesses are arbitrarily large, and the
same construction works for any prescribed positive modulus and positive
number of proper divisors.

**Theorem.** For every $m,r\ge1$ and every bound $B$, there is an integer
$k>B$ with exactly $r+1$ positive divisors such that its increasing list
of proper divisors, reduced modulo $m$, is

$$\underbrace{(1\bmod m,\ldots,1\bmod m)}_{r\text{ entries}}.$$

In particular, taking $m=n$ and $r=2n+1$ gives a witness for A393833 at
every positive index. Since a constant list is a palindrome, the set of
eligible integers is nonempty; the well-ordering of the natural numbers
then gives its least element.

## Proof

We use the classical theorem that, for every positive integer $m$, there
are arbitrarily large primes congruent to $1$ modulo $m$. Only this
special residue class is needed. Mathlib already contains an elementary
cyclotomic proof of it as `Nat.exists_prime_gt_modEq_one`.

Choose such a prime $p>B$ and put

$$k=p^r.$$

Because $p$ is prime, the positive divisors of $k$ are precisely

$$1,p,p^2,\ldots,p^r.$$

They are distinct and increasing, so there are $r+1$ divisors and exactly
$r$ proper divisors. Since $p\equiv1\pmod m$, each proper divisor $p^j$
has residue $1\bmod m$. Thus the reduced list is the constant list in the
theorem. Also $r\ge1$ gives $p^r\ge p>B$. This proves the theorem.

For the original conjecture choose $r=2n+1$ and $m=n$. Then $k=p^{2n+1}$
has exactly $2n+2$ divisors, and the list of its proper divisors modulo
$n$ is a palindrome of length $2n+1$. This includes $n=1$: the common
residue in that case is zero. The existence of a least such $k$ follows
from well-ordering. The construction also proves that there are infinitely
many eligible integers for every fixed $n$.

The construction is an existence proof; its witnesses need not be the
least ones. For example, choosing $p=2$ for $n=1$ yields $k=8$, whereas
the displayed first sequence value is $6$. No minimum values or new
sequence terms are asserted here.

## Exact formal statement

`Proof.lean` defines the residue list using all positive proper divisors,
sorted in increasing order:

```lean
def residues (m k : ℕ) : List ℕ :=
  ((Nat.properDivisors k).sort (· ≤ ·)).map (fun d => d % m)
```

The predicate being proved is:

```lean
def Good (n k : ℕ) : Prop :=
  k.divisors.card = 2 * n + 2 ∧
  (residues n k).length = 2 * n + 1 ∧
  (residues n k).Palindrome
```

The principal theorems are:

| Theorem | Content |
|---|---|
| `prime_power_divisor_count` | A prime power $p^r$ has exactly $r+1$ divisors. |
| `prime_power_residue_list` | For $p\equiv1\pmod m$, the actual sorted residue list is exactly the constant list of length $r$. |
| `arbitrarily_large_constant_lists` | The general theorem for all positive $m,r$ and every bound. |
| `arbitrarily_large_witnesses` | Eligible A393833 integers exceed any given bound. |
| `conjecture` | Every positive index has an eligible integer. |
| `exists_least` | The minimum defining A393833 exists. |

The proof uses mathlib's definitions of divisors, sorting, modular
congruence, and list palindromes. It proves the exact list equality before
deducing palindromicity. There is no replacement sequence, unproved
definition bridge, or finite-index restriction.

## Source, prior work, and scope

`source.seq` preserves the official OEIS data-export record at revision
30, dated April 2, 2026. The entry still explicitly labels existence a
conjecture. Neither its name nor its executable predicates exclude a
constant palindrome. Its PARI predicate tests precisely the divisor
count and equality with the reversed residue list, so the construction
meets the recorded condition.

The source also contains an inconsistent old example for $n=9$:
$19^4 37^3$ has $20$ divisors, but it is not the corrected minimum
$19026866$ in the displayed data. The proof uses neither example and
makes no claim about those minimum computations.

The prime theorem and the elementary divisor formula are classical. They
are credited as existing ingredients, not claimed as new number theory.
The contribution is their explicit application to settle the stated
existence conjecture, the stronger arbitrary-bound formulation, and the
complete Lean proof of the original property. These are reported as one
OEIS conjecture, not as multiple discoveries.

Exact-identifier searches, searches for palindromic proper-divisor
residue lists, and checks of public proof collections did not locate an
earlier proof of this assertion. The bounded search is documented in
`source_checks.md`; it does not certify absolute priority.

## Reproduce

With Elan selecting the pinned toolchain, run from this directory:

```sh
lake exe cache get
lake build
```

The package pins Lean 4.19.0 and mathlib commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`, including transitive
dependencies. `verification.txt` records a fresh package build;
`AUDIT.md` and `audit-verification.txt` record independent review and
compilation. The printed axiom dependencies are only `propext`,
`Classical.choice`, and `Quot.sound`. There are no placeholders,
additional axioms, or `native_decide` calls. `SHA256SUMS.txt` records the
packaged checksums.

### References

- Michel Lagneau, [OEIS A393833](https://oeis.org/A393833), March 1, 2026;
  official [data export](https://github.com/oeis/oeisdata/blob/main/seq/A393/A393833.seq),
  revision 30, April 2, 2026.
- Riccardo Brasca and mathlib contributors,
  [Primes congruent to one](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/NumberTheory/PrimesCongruentOne.lean),
  the existing cyclotomic proof used here.
- Mathlib contributors,
  [divisors of natural numbers](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/NumberTheory/Divisors.lean),
  including the prime-power divisor descriptions.
