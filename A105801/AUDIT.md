# A105801 and A181717 proof audit

Audit date: November 26, 2026, America/Chicago.

## Result

The exact eventual-residue conjectures in [OEIS A105801](https://oeis.org/A105801) and [OEIS A181717](https://oeis.org/A181717) are proved. The proof also establishes a stronger result for every pair of distinct nonnegative integer starting values.

For
$$
a_1=x,\quad a_2=y,\quad
a_{n+2}=\begin{cases}
(a_n+a_{n+1})/2,&a_n+a_{n+1}\text{ even},\\
3(a_n+a_{n+1})+1,&a_n+a_{n+1}\text{ odd},
\end{cases}
$$
and $x\ne y$, the theorem gives
$$
\forall k\ge0\quad\exists N_k\quad\forall n\ge N_k:
\quad 3^k\mid 5a_n+1.
$$
It explicitly identifies the canonical stabilized residue as
$$
r_k=\left\lfloor\frac{(2^k\bmod5)3^k}{5}\right\rfloor
=\frac{(2^k\bmod5)3^k-1}{5}.
$$
The formal proof establishes both the displayed divisibility statement and the eventual equality $a_n\bmod3^k=r_k$.

The specialized theorem `A105801.conjecture` uses seeds $(1,2)$; `A181717.conjecture` uses $(0,1)$. They require no additional assumptions. The generic theorem `FibonacciCollatz.eventual_residue` requires exactly that the two natural-number seeds are distinct.

## Statement fidelity and scope

The source defines the original branch condition and formula directly in `FibonacciCollatz.next`. It defines the sequence using successive ordered pairs and proves its first two values and recurrence. The two OEIS specializations have the correct indexing: the supplied seeds are at indices 1 and 2. Their unused value at index zero has no effect on the recurrence or eventual statement.

The conjecture is for positive exponents; proving the result for every natural exponent, including zero, is stronger. The threshold applies to all later indices, not to a finite range, a subsequence, or merely infinitely many indices.

The arbitrary-power congruences are the usual arithmetic formulation of convergence to $-1/5$ in the 3-adic integers. The Lean source states the result directly in terms of natural-number divisibility and residues. The accompanying paper explains the equivalent 3-adic interpretation. Equal seeds give constant sequences and are correctly excluded from the common-limit assertion for distinct seeds.

## Mathematical review

The argument was checked independently of its formalization.

1. **Persistent inequality.** An averaging step can equal the immediately preceding term only if its two inputs were equal. An expanding step exceeds that preceding nonnegative input. Thus initially distinct adjacent values remain distinct.
2. **Integer descent.** Under averaging, the positive absolute difference of adjacent values halves. Therefore an averaging-only tail is impossible. The formal source uses the natural-number expression `(x-y)+(y-x)` and well-founded induction on that difference.
3. **Arbitrary starting parities.** Initial odd/odd pairs are not assumed admissible. `eventually_admissible_aux` handles them by the same strict descent until a pair contains an even entry. `step_admissible` proves that this property is then preserved. This explicitly validates the claimed generalization to all distinct nonnegative seeds.
4. **Recurring odd terms.** `eventually_odd` proves that every relevant distinct pair eventually reaches an odd second entry. In the preserved parity regime, its first entry is even. This forces two consecutive expanding steps.
5. **Divisibility.** For $b_n=5a_n+1$, the two branches become $(b_n+b_{n+1})/2$ and $3(b_n+b_{n+1})$. Common divisibility by $3^k$ persists through either branch, since 2 is coprime to $3^k$. Two expanding steps make both new entries divisible by $3^{k+1}$. The proof inducts on $k$ and then proves persistence at every later index.
6. **Canonical residue.** The source proves $5r_k+1=(2^k\bmod5)3^k$ and $0\le r_k<3^k$. It proves cancellation of 5 modulo $3^k$, rather than assuming the residue conclusion. These results give the exact eventual remainder equality.

No unproved claim about an infinite supply of expanding steps, a parity pattern, or a valuation increase is left as an assumption of the final result.

The explanatory paper was also reviewed. Its treatment of initially odd/odd seeds is valid. All eight table rows were checked by a separate recurrence implementation: the residues, OEIS indexing, and first indices of certifying adjacent pairs agree with the paper. These finite examples are illustrations; the general proof does not depend on them.

## Formal verification

The exact packaged source was copied to a separate directory and rebuilt from source with no external import path. The commands `lean --version` and `lean -o Proof.olean Proof.lean` both exited with status 0. The compiler was Lean 4.19.0, commit `6caaee842e94`.

The source imports only `Std`, bundled with Lean, and has no Mathlib dependency. The package's fresh `lake build` also succeeded; its record is in `verification.txt`. The separate compilation record is in `audit-verification.txt`.

Source inspection found no `sorry`, `admit`, custom axiom declarations, `native_decide`, unsafe declarations, or replacement implementations. The arithmetic and induction proofs are checked by Lean's kernel.

All five printed theorem reports list only `[propext, Quot.sound]`:

- `FibonacciCollatz.eventual_divisibility`.
- `FibonacciCollatz.eventual_residue`.
- `A105801.eventual_divisibility`.
- `A105801.conjecture`.
- `A181717.conjecture`.

No `sorryAx`, additional axiom, or conditional mathematical hypothesis appears in the specialized conjecture theorems.

## Earlier work and public status

Both retrieved official OEIS entries attribute their arbitrary-power stabilization conjecture to Giovanni Resta on November 17, 2010. They already record eventual residue 7 modulo 9. The retrieved [A105801 internal entry](https://oeis.org/A105801/internal) has revision `#36 Sep 09 2017 20:15:32`. A105801 is attributed to Zak Seidov, September 12, 2006; A181717 to Ralf Stephan, November 17, 2010.

Two directly relevant earlier sources were examined and are acknowledged in the paper:

- [A January 2025 Mathematics Stack Exchange discussion](https://math.stackexchange.com/questions/5028237/) concerns the exact A181717 recurrence. Blue's comment explains preservation of residue 7 modulo 9 after two consecutive terms have that residue. The retrieved discussion does not establish stabilization for arbitrary powers of 3.
- [John Greene's 2008/2009 paper](https://www.fq.math.ca/Papers1/46_47-2/Greene_1-09.pdf), *The Unboundedness of a Family of Difference Equations Over the Integers*, includes the transformed recurrence as its case $c_1=c_2=3,d=6$. The full paper proves ordinary unboundedness/divergence, but contains no arbitrary-power divisibility or 3-adic stabilization theorem. Ordinary divergence is therefore acknowledged as prior work and is not claimed as a new result here.

Searches covered both identifiers, equivalent names and recurrence formulas, the affine-transformed recurrence, and residue, divisibility, stabilization, and p-adic terminology. They also inspected the [trureturing conjecture index](https://www.trureturing.org/conjectures), [Fabian Arevalo's mathematics index](https://fabianarevalo.com/math), and [Eppie's OEIS proof repository](https://github.com/Eppie/oeis-proofs). No earlier proof of the all-powers stabilization assertions was found.

The official text retrieved through the search service still labels both assertions conjectural. Direct downloads of the two internal pages returned HTTP 403 during this review, so this audit does not claim a fresh direct-server snapshot. The novelty conclusion is bounded by the sources searched; it is not an exhaustive claim about unpublished or unindexed work, nor a claim of OEIS acceptance.

## Exact reviewed source

| File | Lines | SHA-256 |
| --- | ---: | --- |
| `Proof.lean` | 376 | `3cf333e44d26ed4f0f47b0e13dc6b7dd2c56b1b4c9d8e9dcb45d95ead2edf11f` |

The proof is self-contained in this source and Lean's standard library. Neither a finite computation nor an external certificate is used as an unproved mathematical premise.
