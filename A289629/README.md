# A289629: eight true power-sum patterns and one false pattern

**Blake Stone** · Proof developed with OpenAI Astra 6.2 · November 26, 2026

## Result and contribution scope

For nonnegative integers $k,n$, write

$$F_k(n)=(k+1)^n+(-k)^n.$$

[OEIS A289629](https://oeis.org/A289629) records a December 3, 2021
conjectural comment by Kevin P. Thompson with nine proposed families of
nonsquarefree values. We classify every listed family on its full stated
domain $m\ge1$: **eight are true, and the fifth is false**.

Four of the true families already follow from formulas in
[A349989](https://oeis.org/A349989). They are credited and formally
reproved for completeness. The contribution accounting is therefore
**four remaining family proofs and one refutation**, together with a
complete Lean verification of all nine branches. The elementary
odd-power factorization used below is established algebra, not a new
general theorem.

| Source branch | Exponent $n$ | $k$ | Result for every $m\ge1$ | Prior status |
|---|---:|---:|---|---|
| 1 | $22m-11$ | 2 | $23^2\mid F_2(n)$ | No earlier exact family proof located in the bounded checks. |
| 2 | $20m-6$ | 3 | $5^2\mid F_3(n)$ | Already covered by A349989's $n\equiv2\pmod4$ formula. |
| 3 | $20m-2$ | 3 | $5^2\mid F_3(n)$ | Already covered by the same A349989 formula. |
| 4 | $3^m$ | 7 | $13^2\mid F_7(n)$ | No earlier exact family proof located in the bounded checks. |
| 5 | $15m$ | 7 | **False:** $F_7(30)$ is squarefree. | Counterexample at $m=2$. |
| 6 | $20m-15$ | 14 | $11^2\mid F_{14}(n)$ | No earlier exact family proof located in the bounded checks. |
| 7 | $16m-8$ | 19 | $17^2\mid F_{19}(n)$ | Already covered by A349989's $n\equiv8\pmod{16}$ formula. |
| 8 | $42m-35$ | 23 | $43^2\mid F_{23}(n)$ | No earlier exact family proof located in the bounded checks. |
| 9 | $8m-4$ | 113 | $17^2\mid F_{113}(n)$ | Already covered by A349989's $n\equiv4\pmod8$ formula. |

These conclusions concern square divisibility, as the conjectural
comment states. They do not assert that the displayed $k$ is the least
eligible value defining A289629. No new sequence terms or minimality
claims are made.

## Proof of the eight true families

### Odd multiples preserve a square divisor

For any integers $X,Y$ and any positive odd integer $t$,

$$X+Y\mid X^t+Y^t.$$

Indeed, the quotient is the alternating polynomial

$$X^{t-1}-X^{t-2}Y+X^{t-3}Y^2-\cdots+Y^{t-1}.$$

Applying this with $X=(k+1)^d$ and $Y=(-k)^d$ gives

$$\boxed{F_k(d)\mid F_k(dt)\quad\text{whenever }t\text{ is odd}.}$$

Consequently, every square divisor of a seed value $F_k(d)$ also divides
all values at odd multiples of the seed exponent. The needed seeds are:

| $k$ | Seed exponent $d$ | Exact value $F_k(d)$ | Square divisor |
|---:|---:|---:|---:|
| 2 | 11 | $175099=23^2\cdot331$ | $23^2$ |
| 3 | 2 | $25=5^2$ | $5^2$ |
| 7 | 3 | $169=13^2$ | $13^2$ |
| 14 | 5 | $221551=11^2\cdot1831$ | $11^2$ |
| 19 | 8 | $42583563041=17^2\cdot147347969$ | $17^2$ |
| 23 | 7 | $1181645977=43^2\cdot639073$ | $43^2$ |
| 113 | 4 | $331943377=17^2\cdot1148593$ | $17^2$ |

Each proposed exponent in a true branch is an odd multiple of the
corresponding seed exponent:

$$\begin{aligned}
22m-11&=11(2m-1),\\
20m-6&=2(10m-3),\\
20m-2&=2(10m-1),\\
3^m&=3\cdot3^{m-1},\\
20m-15&=5(4m-3),\\
16m-8&=8(2m-1),\\
42m-35&=7(6m-5),\\
8m-4&=4(2m-1).
\end{aligned}$$

For $m\ge1$, all the multipliers on the right are positive and odd.
The seed calculations and odd-multiple divisibility therefore prove
all eight families. Since each displayed square is greater than one,
the corresponding values are not squarefree.

## The false fifth branch

The proposed fifth family includes $m=2$, which gives $n=30$ and $k=7$.
Its value is

$$\begin{aligned}
F_7(30)&=8^{30}+7^{30}\\
&=1260479379576072532986987473\\
&=113\cdot3361\cdot25741\cdot12001921\cdot10742679301.
\end{aligned}$$

All five factors are distinct primes, so this number is squarefree.
This is a counterexample to the exact universally quantified claim.
The formal proof checks both the product identity and primality of
every factor; a numerical factorization oracle is not a proof premise.

### Explicit certificate for the largest prime

To keep the largest primality check compact, the Lean proof uses the
classical Lucas criterion. If $a^{p-1}=1$ modulo $p$ and
$a^{(p-1)/q}\ne1$ modulo $p$ for every prime divisor $q$ of $p-1$,
then $p$ is prime. This criterion is already proved in mathlib.

First, for $p=35808931$ use base $a=3$ and

$$p-1=2\cdot3^2\cdot5\cdot23\cdot17299.$$

The full power has residue one. The powers with exponents $(p-1)/q$
have the following residues:

| $q$ | Residue modulo $35808931$ |
|---:|---:|
| 2 | 35808930 |
| 3 | 1193830 |
| 5 | 21860597 |
| 23 | 6523943 |
| 17299 | 6900949 |

Next, for $p=10742679301$ use base $a=2$ and

$$p-1=2^2\cdot3\cdot5^2\cdot35808931.$$

Again the full power has residue one, while the required proper powers
have residues:

| $q$ | Residue modulo $10742679301$ |
|---:|---:|
| 2 | 10742679300 |
| 3 | 5670453206 |
| 5 | 4923777471 |
| 35808931 | 9590149649 |

None is one. The finite modular calculations are established by
kernel-checked modular exponentiation. The remaining primality checks
and coprimality checks are also verified in Lean.

### A valid correction

The fifth branch becomes true after restricting $m$ to odd positive
integers:

$$\boxed{m\text{ odd}\quad\Longrightarrow\quad13^2\mid F_7(15m).}$$

The seed $F_7(3)=13^2$ divides $F_7(15)$, and an odd multiplier $m$
preserves its square divisor. More generally, the same argument covers
every odd multiple of exponent three. No claim that all even values of
$m$ give squarefree numbers is made.

## Formal statements and reproduction

`Proof.lean` begins with the literal integer expression

```lean
def value (k n : ℕ) : ℤ :=
  (k + 1 : ℤ) ^ n + (-(k : ℤ)) ^ n
```

`odd_multiple_dvd` proves the general divisibility rule. The declarations
`pattern_1` through `pattern_9`, omitting `pattern_5`, supply explicit
square divisors for all eight true branches. `eight_true_patterns`
states all eight nonsquarefreeness conclusions together for every
$m\ge1$. `counterexample_squarefree` proves squarefreeness of the exact
integer at $(k,n)=(7,30)$, and `pattern_5_false` negates the universal
fifth claim. `pattern_5_corrected` gives its valid odd-$m$ restriction.

The package pins Lean 4.19.0 and mathlib commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. With the pinned toolchain
selected, run in this directory:

```sh
lake exe cache get
lake build
```

The reported axioms are only `propext`, `Classical.choice`, and
`Quot.sound`. The source has no unfinished proofs, custom axioms, or
`native_decide` calls. See `verification.txt` for the fresh package build,
and the accompanying audit files for the separate review and compilation.

## Sources and limits

The main snapshot is A289629 revision 60, January 10, 2022. The related
A349989 snapshot is revision 30, February 24, 2022, and explicitly
records the four credited branches. Both were retrieved on November
26, 2026. The direct OEIS result also retained the nine-family
conjectural comment at the time checked.

`source_checks.md` records the exact snapshots, linked background, and
bounded searches for earlier resolutions. These checks do not establish
exhaustive historical priority or OEIS editorial acceptance. The
contribution is the explicit correction and formal classification of
the recorded claim, with previously established cases identified.
