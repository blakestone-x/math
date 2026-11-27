# Independent audit: A389524 weighted orphan identity

**Verdict: PASS.** The exact delivered modules prove Conjecture 2 for
every positive integer, starting from the original recursive triangle
and the literal orphan solution set. The proof includes both definition
bridges and does not assume an unproved generating-function identity.

Reviewed November 26, 2026 (America/Chicago), by a separate agent from
the two authors of the new proof modules. This is an internal independent
review, not an external journal review or a certification of priority.

## Exact sources and fresh compilation

All four modules were read in full. The frozen sources have SHA-256:

| Module | SHA-256 |
|---|---|
| `Uchimura.lean` | `878257266d1ebc4e4f1791dc18a3a2d9b7c6e0d323d4ecaecc8ecfe74423305a` |
| `Triangle.lean` | `ed482386e996977341ad53209a9a9cca5c827c1f86d18da11977ab5c3b288a10` |
| `Orphans.lean` | `1462d5dd856d0b192c5b7a1d788359133bb6ed58a25dbfb9fe94e450ab66faa2` |
| `Weighted.lean` | `d433a2310fd39ec894ec67a972e8a64c1ed3355bd17b1e8773b3ad881c9d89ca` |

The files were copied into a fresh isolated directory and compiled in
dependency order with Lean 4.19.0 and the pinned mathlib revision
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. Each local module's compiled
artifact was produced by this invocation; only mathlib and its dependency
caches were reused. All four invocations exited successfully, without
warnings or errors. The exact conditions, hashes, and output are recorded
in `audit-verification.txt`.

Every printed public theorem's axiom report contains only `propext`,
`Classical.choice`, and `Quot.sound`. A separate scan of executable source
found no `sorry`, `admit`, custom axiom declaration, `native_decide`, or
unsafe proof implementation.

The reproduced `Uchimura.lean` is byte-for-byte identical to the earlier
package. The mathematical body of `Triangle.lean` is likewise unchanged;
its revised introductory comment accurately distinguishes the earlier
Conjectures 1 and 3 from this extension's Conjecture 2.

## Correspondence to the original assertion

The preserved A389524 source, revision 19 of October 22, 2025, records
the reversed weighted-row conjecture for A274628. The live source page
still displayed that assertion when checked.

`A389524.triangle` retains the original integer-valued recurrence,
including negative entries and the exceptional first column: its value
is one at n=1 and zero at every other index. The subtraction sum is merely
reindexed. `triangle_eq_column` proves the column-polynomial bridge by
strong induction from that recurrence; the column formula is not used
as an alternate unverified definition.

The A274628 snapshot's literal interpretation is the number of solutions
to `a*b-c*d=n`, with `a>c>=0` and `b>d>=0`.
`Nathanson.Orphan n` is exactly this nonnegative integer structure.
Its determinant equality `a*b = n+c*d` is equivalent to the source's
integer equation. There is no additional coordinate bound in the
definition. The proof derives finiteness from these conditions.

The final `weighted_row` proves the usual order, summing `k*T(n,k)` for
1<=k<=n. `original_conjecture` proves the exact reversed finite row by
the bijection k |-> n-k+1. The theorem assumes only n>0, the source's
full index range.

As a separate interpretation check, an independent implementation of
the original recurrence and a direct enumeration of the literal orphan
solutions matched all first 30 values in the A274628 snapshot. This
finite check was not used as a proof premise.

## Literal orphan counting

The proof of `Orphan.bounds` shows that every coordinate is at most n.
The resulting finite instance therefore counts the entire originally
unbounded set.

The solutions with c=0 are in explicit bijection with a divisor b of n
and an element of `Fin b`. Their cardinality is the sum of the divisors.
The solutions with c>0 correspond bijectively to positive quadruples
`(x,y,z,w)` with `x*y+z*w=n` and w<=y, under
`(x,y,z,w)=(a-c,b,c,b-d)`. The inverse is
`(a,b,c,d)=(x+z,y,z,y-w)`; the order condition supplies exactly the
nonnegativity needed for d. Both inverse identities are formally proved.

The unrestricted positive quadruples are counted by the convolution
of the positive-divisor counts. Swapping the two ordered products
exchanges w<y with y<w. The fixed boundary w=y is explicitly parameterized
by a divisor r=x+z and one of its r-1 positive splits. This gives

```text
2 * orphanCount n + d(n) = convolution n + 3 * sigma n.
```

No formula for the orphan count is assumed in this derivation. The
formal zero-index extension uses `Nat.divisors 0 = ∅`; the OEIS theorem
and its ordinary positive-divisor interpretation concern n>0.

## Finite weighted identity

The algebra is developed over an arbitrary commutative ring with a
nilpotent element q satisfying q^(N+1)=0. The geometric inverses of
1-q^i are constructed, so the apparent denominators do not add a
nonvanishing assumption or a formal-power-series convergence premise.

The marked recurrence is checked against the unmarked column recurrence.
Its coefficient formula has the correct product endpoints. The block
product difference telescopes with lower endpoint zero and upper
endpoint one. All extensions of finite summation ranges add only powers
that nilpotence makes zero. Differentiating this finite marked identity
produces the weighted Lambert sum E.

The reproduced product identity `H*G=P` is proved from polynomial scaling
and nilpotence. The first and second derivatives are then computed
explicitly. The second moment is `D^2+E`; in particular, the square
Lambert term, divisor-sum term, and signs agree with the classical
second-moment formula.

For the remainder `k*R_k-F'_k(1)`, the recurrence and finite tail-product
identities give the missing contribution. Combining them proves

```text
2 * weightedRows q N = D^2 - D + 3*E.
```

This is first proved without division by two. Specialization to the
quotient of integer polynomials by X^(N+1) and the divisibility criterion
for X powers makes coefficient extraction valid at every degree <=N.
Weighted factor-pair bijections identify the coefficients of D and E
with the literal divisor statistics; the polynomial convolution formula
identifies the coefficient of D^2. The endpoint coefficients at zero
vanish, so the convolution has exactly the source's range 1 through n-1.
Cancellation of two is performed only after passing to integers.

## Written proof, sources, and assertion count

The completed `README.md` and `source_checks.md` were reviewed against
the source snapshots and formal declarations. The finite marker argument,
second moment, remainder recurrence, original orphan bijections, and
coefficient bridge all agree. A minor prose ambiguity about the
formal zero-index divisor convention was corrected by restricting the
README's statement to the required positive indices. This did not affect
the theorem or any proof term.

The weighted section of the accompanying manuscript was also independently
read against the modules, including all product endpoints, signs,
index shifts, and positive-index restrictions. No mathematical correction
was required.

The documentation credits the classical Uchimura and Bressoud--Subbarao
identities and the earlier orphan formulas. The primary manuscript
arXiv:2210.03457 was independently opened: equation (1.5) records the
generalized divisor weight, and Theorem 1.1 and equation (1.9) explicitly
record the classical second-moment ingredient. The new assertion is
the precise connection to the recursive 2025 triangle.

The current public trureturing index was reopened and searched for
A389524, A274628, orphan, and Uchimura, with no matches. The complete
enumerated targets in the author-submitted abstracts of *Low-Hanging
Fruit* I--V were reopened and contain neither target. Both search engines
were also used for exact and semantic resolution queries. No earlier
resolution of this exact connection was located. These checks have
the bounded scope accurately stated in `source_checks.md`.

The correct contribution count is **one additional recorded assertion**.
The earlier Conjectures 1 and 3, the classical identities, and the helper
counting results are not counted again. No historical-priority or OEIS
editorial-acceptance claim is made.
