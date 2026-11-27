# Independent audit of A016789

Reviewer: root agent, separate from the agent that developed the proof.
Date: November 26, 2026 (America/Chicago).

## Result

**PASS.** The final theorem proves the literal negabinary XOR conjecture
in A016789 for every natural-number index, including zero. The source
was independently compiled in a fresh directory with Lean 4.19.0 and
mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

Reviewed `Proof.lean` SHA-256:

`7873db8e0f11d9f59e6315e9848d274a1d4f798bb24f8f899a89586ee6dbab86`

The compiler output and exact verification environment are recorded in
`audit-verification.txt`. The original source hash was checked again
after compilation. The displayed axiom lists contain only `propext`,
`Classical.choice`, and `Quot.sound`.

## Statement and definition review

The source formula is `a(n) = n XOR A005351(n+1) XOR A005352(n+1)`, with
`a(n)=3*n+2` and offset zero. A005351 reads the base-minus-two digits of
the positive input as binary; A005352 does the same for the negated input.
The formal map `value` literally evaluates `Nat.digits 2 code` using
`Nat.ofDigits (-2 : ℤ)`. Thus its inverse is the required binary reading
of a negabinary representation.

The proof establishes both injectivity of `value` and existence of codes
for each signed input. Consequently the two choice-defined code
functions are uniquely determined by the original definitions. No
unproved conversion formula or OEIS recurrence is assumed. Extending the
negative-input sequence to zero is legitimate for the induction; the
target itself always evaluates it at the positive index `n+1`.

`original_conjecture` makes the bridge explicit: for any literal binary
codes whose base-minus-two values are `n+1` and `-(n+1)`, the three-way
XOR equals `3*n+2`. The auxiliary existence theorem prevents this direct
formulation from depending on potentially nonexistent representations.

## Proof review

1. The low-bit recurrence uses the standard base-two digit decomposition.
   Its parity argument forces equal low bits for equal negabinary values;
   division by two decreases the sum of the two codes. This proves
   injectivity without assuming uniqueness of a signed-base expansion.
2. Simultaneous existence for positive and negative inputs covers zero
   and one explicitly. For larger inputs both half-sized induction
   arguments are strictly smaller. The negative odd case uses the ceiling
   half, as required.
3. All four encoding recurrences are derived from evaluation and
   injectivity. The shifted argument in `negative_odd` is correct.
4. The three XOR identities are proved together. All six parity branches
   use only the smaller index `n/2`; none assumes the desired theorem at
   the same or a larger index. Each branch uses Lean's natural-number XOR
   operations and checked low-bit identities.
5. The conjecture is the third component with its equality reversed to
   match the source. Zero gives `0 XOR 1 XOR 3=2` exactly.

The README's six recurrence branches match the Lean proof. Its examples,
initial values, index convention, and count of one recorded conjecture
are consistent with the preserved OEIS records.

## Scope and prior work

The reviewed result is the specific triple-XOR formula. Standard
negabinary representation and conversion facts are credited to prior
work, including Arndt's treatment. The source notes record a bounded
search and do not assert absolute priority. The two companion identities
support the one conjecture and are not counted as separate conjectures.

No proof placeholders, custom axioms, `native_decide`, or finite-domain
replacement of the universal theorem were found.
