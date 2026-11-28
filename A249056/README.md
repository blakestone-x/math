# Mathar’s recurrence for OEIS A249056

For every nonnegative integer $n$, put $h=\lfloor n/2\rfloor$ and define
$$
a(n)=\prod_{i=1}^{h}(2n-i)(2n+i).
$$
The first terms are $1,1,15,35,3780,9504$. In July 2022 R. J. Mathar conjectured an explicit recurrence of order three,
$$
c_0(n)a(n)+c_1(n)a(n-1)+c_2(n)a(n-2)+c_3(n)a(n-3)=0.
$$
The Lean proof establishes it for every $n\ge3$ with the four polynomials as printed in OEIS. Their exact coefficients are in the statement file. [OEIS A249056](https://oeis.org/A249056) · [Left to Solve](https://lefttosolve.com/p/oeis-a249056) · [Statement](statements/oeis-a249056.lean) · [Proof](proofs/oeis-a249056.lean)

## Why the recurrence holds

For $n>0$, the factors in the product cover the entire interval $[2n-h,2n+h]$ except its midpoint $2n$. Hence
$$
a(n)=\frac{(2n+h)!}{2n(2n-h-1)!}.
$$
The proof verifies this identity by induction on the number of pairs in the product. Each step appends one factor at either end of the interval.

At $n=3$, substitution of $a(3)=35$, $a(2)=15$, $a(1)=1$, and $a(0)=1$ gives zero. For $n\ge4$, write $n=2m+4$ or $n=2m+5$. Every term is then of the form
$$
a(2m+j)=
\frac{(5m+2j+\lfloor j/2\rfloor)!}
{(4m+2j)(3m+2j-\lfloor j/2\rfloor-1)!},\qquad 1\le j\le 5.
$$
For example, the four shifts in the even case are $j=4,3,2,1$. Each numerator factorial expands to $(5m)!$ times a fixed finite product. Each denominator factorial expands similarly from $(3m)!$. Substitution in the conjectured recurrence leaves one polynomial identity in $m$ for each parity. Lean clears the positive denominators and normalizes both polynomials to zero.

## Verify the proof locally

The commands below use Git, Bash, and [Elan](https://github.com/leanprover/elan). Run them from the directory containing this README. The tagged mathlib checkout requests Lean 4.33.1. The cache command downloads the dependencies used in the statement and proof.

```bash
source_dir=$PWD
check_dir=$(mktemp -d)
git clone --depth 1 --branch v4.33.1 https://github.com/leanprover-community/mathlib4 "$check_dir/mathlib"
cd "$check_dir/mathlib"
lake exe cache get Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean Mathlib/Data/Rat/Defs.lean Mathlib/Data/Nat/Factorial/Basic.lean Mathlib/Tactic/FieldSimp.lean Mathlib/Tactic/NormNum.lean Mathlib/Tactic/Ring.lean Mathlib/Tactic/Positivity.lean
mkdir -p OMAStatements
cp "$source_dir/statements/oeis-a249056.lean" OMAStatements/S_oeis_a249056.lean
cp "$source_dir/proofs/oeis-a249056.lean" VerifyA249056.lean
printf '\n#print axioms OMA.solution\n' >> VerifyA249056.lean
lake env bash -ec '
  export LEAN_PATH="$PWD:$LEAN_PATH"
  lean -o OMAStatements/S_oeis_a249056.olean OMAStatements/S_oeis_a249056.lean
  lean VerifyA249056.lean
'
```

The statement file declares the board’s target with its required placeholder. The separate proof establishes that target. The axiom audit reports exactly `propext`, `Classical.choice`, and `Quot.sound`.

[Board submission](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/18237) · [Local kernel verdict for the complete proof](proof-verdict.json)
