# A016789: Breysens's negabinary XOR identity

**Blake Stone** · Proof developed with OpenAI Astra 6.2 · November 26, 2026

## The conjecture and result

Let P(m) be the nonnegative integer obtained by writing m in base −2
and then reading the same digits in base 2. Let N(m) do the same for −m.
Thus P is [OEIS A005351](https://oeis.org/A005351), and N on positive
indices is [OEIS A005352](https://oeis.org/A005352). We extend N to zero
by N(0)=0 for the proof.

Gilian Breysens's July 21, 2017 conjecture in
[OEIS A016789](https://oeis.org/A016789) is

$$\boxed{n\mathbin{\oplus}P(n+1)\mathbin{\oplus}N(n+1)=3n+2
\qquad(n\ge0),}$$

where $\oplus$ means bitwise exclusive OR on nonnegative integers.
We prove it for every index. The right-hand side is the defining formula
for A016789; the new assertion addressed here is its equality to the
three-way XOR of the specified sequences.

The argument also proves two companion identities:

$$
n\mathbin{\oplus}P(n)\mathbin{\oplus}N(n)=3n,
\qquad
n\mathbin{\oplus}N(n)\mathbin{\oplus}P(n+1)=3n+1.
$$

These support the proof of the one recorded conjecture; they are not
counted as additional OEIS conjectures.

For example, P(1)=1 and N(1)=3, so the n=0 case reads 0 XOR 1 XOR 3=2.
At n=1, the codes are P(2)=6 and N(2)=2, giving 1 XOR 6 XOR 2=5.
At n=2 they are P(3)=7 and N(3)=13, giving 2 XOR 7 XOR 13=8.

## Proof

### 1. Literal negabinary representations

For a nonnegative binary code c, let its ordinary binary digits be
$b_0,b_1,\ldots,b_\ell$, with the least significant digit first, and put

$$V(c)=\sum_{i=0}^{\ell}b_i(-2)^i.$$

This directly expresses reading that same zero-one string in base −2.
Appending a low bit b, where b is zero or one, gives

$$V(2c+b)=b-2V(c). \tag{1}$$

The map V is injective. If V(c)=V(d), reducing (1) modulo two shows
that c and d have the same low bit. Subtracting those equal bits and
cancelling −2 shows that their truncated codes also have equal values.
Repeated division by two eventually reaches zero, so all their bits
agree and c=d.

Every integer has such a code. One can show existence for m and −m
simultaneously by strong induction on m. The cases m=0 and m=1 use
codes 0, 1, and 3. For m≥2, put

$$b=m\bmod2,\qquad u=\lfloor m/2\rfloor,
\qquad v=\lceil m/2\rceil.$$

Both u and v are smaller than m. A code c for −u produces a code
2c+b for m, by (1). A code d for v produces a code 2d+b for −m.
Together with injectivity, this proves existence and uniqueness.
Consequently P(m) and N(m) are exactly the unique codes satisfying
V(P(m))=m and V(N(m))=−m.

### 2. The four encoding recurrences

Equation (1) and uniqueness give, for every m≥0,

$$
\begin{aligned}
P(2m)&=2N(m), & N(2m)&=2P(m),\\
P(2m+1)&=2N(m)+1, & N(2m+1)&=2P(m+1)+1.
\end{aligned} \tag{2}
$$

For the last identity, the proposed code has value
1−2(m+1)=−(2m+1). All four identities are derived from the original
representations; they are not substituted as unproved definitions of
the OEIS sequences.

### 3. Three XOR expressions

Define

$$
\begin{aligned}
S_0(m)&=m\mathbin{\oplus}P(m)\mathbin{\oplus}N(m),\\
S_1(m)&=m\mathbin{\oplus}N(m)\mathbin{\oplus}P(m+1),\\
S_2(m)&=m\mathbin{\oplus}P(m+1)\mathbin{\oplus}N(m+1).
\end{aligned}
$$

For b,c in {0,1}, binary XOR obeys

$$(2x+b)\mathbin{\oplus}(2y+c)
=2(x\mathbin{\oplus}y)+(b\mathbin{\oplus}c). \tag{3}$$

Applying (2) and (3), and using associativity and commutativity of XOR,
gives the following exact recurrences:

| Expression | At 2m | At 2m+1 |
|---|---|---|
| S₀ | 2S₀(m) | 2S₁(m)+1 |
| S₁ | 2S₀(m)+1 | 2S₂(m) |
| S₂ | 2S₁(m) | 2S₂(m)+1 |

For instance, the even case in the final row is

$$
\begin{aligned}
S_2(2m)
&=(2m)\mathbin{\oplus}(2N(m)+1)
          \mathbin{\oplus}(2P(m+1)+1)\\
&=2\bigl(m\mathbin{\oplus}N(m)\mathbin{\oplus}P(m+1)\bigr)
=2S_1(m).
\end{aligned}
$$

At zero, P(0)=N(0)=0, P(1)=1, and N(1)=3, giving

$$S_0(0)=0,\qquad S_1(0)=1,\qquad S_2(0)=2.$$

Strong induction now proves $S_i(m)=3m+i$ for i=0,1,2 simultaneously.
For a positive index, each recurrence uses only the smaller index
$\lfloor m/2\rfloor$. Substitution verifies every branch; for example,
$S_1(2m+1)=2(3m+2)=3(2m+1)+1$ and
$S_2(2m)=2(3m+1)=3(2m)+2$.
The case i=2 is exactly Breysens's conjecture.

## Formalization and definition bridge

`Proof.lean` defines

```lean
def value (code : ℕ) : ℤ :=
  Nat.ofDigits (-2 : ℤ) (Nat.digits 2 code)
```

Both functions are mathlib's standard digit operations. Thus the definition
literally evaluates the ordinary binary digits in base −2. The file proves
`value_injective` and `codes_exist` before defining `positiveCode` and
`negativeCode` as their unique representatives. The uniqueness theorems
identify these functions with the original OEIS descriptions. Leading
zeroes make no difference because the same string read as a binary integer
has the same code.

`three_identities` proves the three expressions above jointly, and
`conjecture` states the claimed identity using the uniquely characterized
codes. The final `original_conjecture` also states the identity directly
for any two binary codes p and q whose base −2 evaluations are n+1 and
−(n+1). Existence and uniqueness of those codes are proved in the same
file. No alternative sequence recurrence, digit conversion, finite-index
bound, or original-definition bridge is assumed.

The proof is checked with Lean 4.19.0 and mathlib v4.19.0 at commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. Printed theorem dependencies
are only the standard axioms `propext`, `Classical.choice`, and
`Quot.sound`. There are no placeholders, additional axioms, or
`native_decide` calls.

## Sources, prior work, and scope

The preserved primary records are:

- `source.seq`: A016789, revision 305, July 11, 2026;
- `A005351.seq`: revision 81, June 28, 2026;
- `A005352.seq`: revision 66, June 27, 2025.

They were retrieved from the official OEIS-maintained data export on
November 26, 2026 in America/Chicago. The A016789 record still explicitly
labels the XOR identity a conjecture. A different conjecture on that page,
concerning cubes modulo three, is marked proved; it is unrelated to the
identity settled here.

Jörg Arndt's [*Matters Computational*](https://www.jjj.de/fxt/fxtbook.pdf),
section 1.22, pages 58–60, gives the standard negabinary definition,
binary conversion algorithms, the positive and negative sequences,
and increment/decrement algorithms. Those facts are prior work. The
section does not state the three-way XOR identity proved here.

Exact-identifier, exact-expression, and negabinary/XOR searches, together
with checks of the public trureturing, Fabian Arevalo, and Eppie proof
collections, did not locate an earlier proof of this assertion. A further
compendium PDF reproduces the OEIS identity with the label “conjectured”
and supplies no proof. The bounded search and source hashes are recorded
in `source_checks.md`; absence of a located proof is not a guarantee of
absolute publication priority.

## Reproduce

With Elan selecting the pinned toolchain, run from this directory:

```sh
lake exe cache get
lake build
```

The lakefile pins mathlib and the manifest locks all transitive dependencies.
`verification.txt` records a fresh build of this exact source. Independent
review and compilation are recorded in `AUDIT.md` and
`audit-verification.txt`. `SHA256SUMS.txt` provides checksums for the
packaged files.
