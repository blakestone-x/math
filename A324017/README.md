# A324017: two tetration proofs and a counterexample

**Blake Stone** · Proof developed with OpenAI Astra 6.2 · November 26, 2026

## Results

Let $T_0(a)=1$ and $T_{m+1}(a)=a^{T_m(a)}$. This is ordinary integer
tetration. [OEIS A324017](https://oeis.org/A324017), introduced by Davis
Smith on March 28, 2019, defines

$$A(m,n)=T_m(2n-1)\bmod(2n)^m.$$

Its three recorded conjectures are resolved as follows:

| Recorded assertion | Result |
|---|---|
| If $T_m(2n-1)\equiv k\pmod{(2n)^m}$, then $(2n-1)^k\equiv k\pmod{(2n)^m}$, for $m,n,k>1$. | **Proved**, with the broader ranges $m,n\ge1$ and $k\ge0$. |
| For $n>1$, $m\ge2$, the quotient $\lfloor T_m(2n-1)/(2n)\rfloor$ is $2(n-1)$ modulo $2n$. | **Proved** for the full stated domain. |
| If $T_m(2n-1)\equiv j\pmod{(2n)^{m+1}}$, then $A(m+1,n)=j$, for $m>1$. | **False as written**, even when $j$ is required to be the least nonnegative residue. |

The counterexample is $m=n=2$ and $j=27$:

$$T_2(3)=3^3=27\equiv27\pmod{64},\qquad
A(3,2)=3^{27}\bmod64=59\ne27.$$

The defect is present within the canonical residue range $0\le j<64$.
It does not depend on choosing an out-of-range representative of the
congruence class.

We also prove the valid compatibility relation

$$\boxed{A(m+1,n)\bmod(2n)^m=A(m,n)\qquad(m,n\ge1).}$$

Thus increasing the tower height preserves the first $m$ digits in base
$2n$. The third conjecture asks for the additional next digit to have
already stabilized; the counterexample shows why that stronger claim
fails.

## Proof of the first conjecture

Throughout, write $b=2n\ge2$ and $a=b-1$, so $b$ is even and $a$ is odd.

### 1. A lifting lemma

If $r\ge1$ and $x\equiv1\pmod{b^r}$, then

$$x^b\equiv1\pmod{b^{r+1}}. \tag{1}$$

Indeed,

$$x^b-1=(x-1)(1+x+\cdots+x^{b-1}).$$

The first factor is divisible by $b^r$. Since $x\equiv1\pmod b$, the
second factor is congruent to $b$, hence zero modulo $b$. Their product
is divisible by $b^{r+1}$.

The binomial theorem, retaining the constant and linear terms modulo
$b^2$, gives

$$a^b=(-1+b)^b\equiv1-b^2\equiv1\pmod{b^2}.$$

Applying (1) repeatedly proves

$$\boxed{a^{b^r}\equiv1\pmod{b^{r+1}}\quad(r\ge1).} \tag{2}$$

Consequently, whenever $u\equiv v\pmod{b^r}$,

$$a^u\equiv a^v\pmod{b^{r+1}}. \tag{3}$$

For completeness, no subtraction of exponents is needed: write each
nonnegative exponent as its common remainder modulo $b^r$ plus a
nonnegative multiple of $b^r$, and apply (2).

### 2. Stabilization at the required height

All the towers $T_m(a)$ are odd. Since $a\equiv-1\pmod b$, every
positive-height tower is congruent to $-1$ modulo $b$. In particular,
$T_2(a)\equiv T_1(a)\pmod b$.

Inductively, if $T_{m+1}(a)\equiv T_m(a)\pmod{b^m}$, then (3) gives

$$T_{m+2}(a)=a^{T_{m+1}(a)}
\equiv a^{T_m(a)}=T_{m+1}(a)\pmod{b^{m+1}}.$$

Therefore

$$\boxed{T_{m+1}(a)\equiv T_m(a)\pmod{b^m}\quad(m\ge1).} \tag{4}$$

Now suppose $T_m(a)\equiv k\pmod{b^m}$. Equation (3), followed by
reduction modulo $b^m$ and then (4), gives

$$a^k\equiv a^{T_m(a)}=T_{m+1}(a)
\equiv T_m(a)\equiv k\pmod{b^m}.$$

This proves the first conjecture on its full domain and the slightly
broader ranges stated above.

## Proof of the second conjecture

For any odd positive exponent $E$, the same first-order binomial
expansion gives

$$a^E=(-1+b)^E\equiv-1+bE\pmod{b^2}. \tag{5}$$

If $m\ge2$, the exponent $E=T_{m-1}(a)$ is odd and satisfies
$E\equiv-1\pmod b$. Substituting in (5) yields

$$T_m(a)\equiv-b-1\pmod{b^2}.$$

For $b\ge2$, its least nonnegative residue is

$$b^2-b-1=b(b-2)+(b-1). \tag{6}$$

For any nonnegative integer $t$ and positive $b$,

$$\left\lfloor\frac{t}{b}\right\rfloor\bmod b
=\left\lfloor\frac{t\bmod b^2}{b}\right\rfloor.$$

Using (6) gives

$$\left\lfloor\frac{T_m(2n-1)}{2n}\right\rfloor
\equiv b-2=2(n-1)\pmod b,$$

as claimed. The underlying residue formula also holds at $n=1$.

## Disproof and corrected statement

At $n=m=2$, the third conjecture compares $T_2(3)$ and $T_3(3)$ modulo
$4^3=64$. The first is $27$. For the second, modular arithmetic gives

$$3^{27}\equiv59\pmod{64}.$$

Both computations are checked by Lean, giving a counterexample to the
universal statement even after explicitly requiring $0\le j<64$.

Equation (4) proves the replacement relation. Since $b^m$ divides
$b^{m+1}$, taking $T_{m+1}(a)$ first modulo $b^{m+1}$ and then modulo
$b^m$ is the same as reducing directly modulo $b^m$. The result is
$T_m(a)\bmod b^m=A(m,n)$.

The source's illustrative array indices are also transposed: its
displayed table places $563$ at $A(3,6)$ and $16115$ at $A(4,6)$,
whereas the comment writes $A(6,3)$ and $A(6,4)$. The disproof addresses
the explicitly written quantified claim; it does not infer an intended
replacement from those inconsistent examples.

## Formal statement and verification

`Proof.lean` begins with the literal recursive definitions:

```lean
def tower (a : ℕ) : ℕ → ℕ
  | 0 => 1
  | m + 1 => a ^ tower a m

def array (m n : ℕ) : ℕ :=
  tower (2 * n - 1) m % (2 * n) ^ m
```

| Declaration | Checked content |
|---|---|
| `period` | Equation (2), for every positive $n,r$. |
| `stabilization` | Equation (4), for all positive $m,n$. |
| `fixed_point` | The first conjecture, with broader ranges. |
| `square_residue` | Exact least residue (6), for every height at least two. |
| `quotient_conjecture` | The second conjecture on its stated domain. |
| `third_claim_counterexample` | The canonical counterexample and both exact residues. |
| `third_claim_false` | Negation of the universally quantified third claim, even restricted to canonical residues. |
| `corrected_compatibility` | The valid reduction relation between adjacent rows. |

All towers in the universal theorems are the original integer towers;
there is no approximation by an iterated remainder algorithm. The
counterexample arithmetic uses kernel-checked `norm_num`, not
`native_decide`. The public axiom reports use only `propext`,
`Classical.choice`, and `Quot.sound`. No placeholders or new axioms occur.

## Prior work and contribution scope

Modular tetration, eventual stabilization, and exponential fixed points
are classical. The source links Charles W. Trigg's Problem 559 in *Crux
Mathematicorum* 7 (1981), page 192, whose discussion concerns decimal
expomorphic numbers. Daniel B. Shapiro's later solution in volume 13
(1987), pages 291–294, proves decimal lifting and uniqueness. Daniel B.
Shapiro and S. David Shapiro's *Iterated Exponents in Number Theory*
(2007) treats general modular stabilization and fixed points.

J. Jiménez Urroz and J. Luis A. Yebra's *On the Equation $a^x\equiv x$
$(\bmod\ b^n)$* (2009) also develops a general lifting framework, including
the role of congruences of the form (2). These methods are existing
mathematics and are credited here. This package gives elementary
specializations for every even modulus base $b$ with exponential base
$b-1$, proves the exact two claims in A324017, and formally refutes the
third literal claim. It does not claim a new general theory of tetration.

The retrieved official OEIS export is revision 91, February 16, 2025;
all three comments remain labeled conjectures. Bounded searches and
checks of related proof collections did not locate an earlier exact
resolution. That does not establish absolute priority. The search record
and references are in `source_checks.md`.

## Reproduce

With the pinned toolchain selected, run from this directory:

```sh
lake exe cache get
lake build
```

The package pins Lean 4.19.0 and mathlib commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`; the manifest locks transitive
dependencies. `verification.txt` records a fresh package build.
`AUDIT.md` and `audit-verification.txt` record independent review and
compilation. `SHA256SUMS.txt` records the deliverable checksums.
