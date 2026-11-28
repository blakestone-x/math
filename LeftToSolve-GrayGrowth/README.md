# Gray recurrences: two checked contributions for Left to Solve

Blake Stone · November 27, 2026

This package contains exact Lean statements and complete matching proofs for
[OEIS A265385](https://oeis.org/A265385) and
[OEIS A265386](https://oeis.org/A265386), prepared for
[Left to Solve](https://lefttosolve.com).

**Status:** both proposed statements and their full proofs compile locally on
the site's pinned Lean 4.33.1 environment. They have not been submitted to or
accepted by Left to Solve. Both catalog entries were unformalized when claimed.
The site requires human review and merge of each statement before its companion
proof becomes eligible for a proof submission.

The two growth-limit proofs come from the existing A265385 and A265386 packages
in this repository. This work ports them to the site's current environment and
adds exact statements of persistent oscillation. The three-state oscillation
proof for A265385 is an extension developed during this work; no worldwide
priority claim is made.

## Exact results

Write G(m) = m XOR floor(m/2). Both sequences start with a(1) = a(2) = 1.

| Entry | Recurrence for n ≥ 3 | Limit of (a(2n)/a(n))^(1/n) |
| --- | --- | --- |
| A265385 | a(n) = G(a(n−1) + a(n−2)) | 2 |
| A265386 | a(n) = G(G(a(n−1)) + G(a(n−2))) | √2 |

For each sequence, put s(n) = a(n)/a(n−1). The complete statement also proves
that there is a fixed ε > 0 such that, beyond every index N, some ratio is below
the corresponding limit minus ε and some ratio is above the limit plus ε.

This is an explicit interpretation of the source's qualitative description of
persistent fluctuations. The OEIS comments do not prescribe numerical values
for ε. In particular, the approximate “1%” description in A265385 is not treated
as an exact bound.

### New A265385 oscillation proof

For every k ≥ 0, the normalized binary-prefix pair

\[
\left(
\left\lfloor a(k+9)/2^k\right\rfloor,
\left\lfloor a(k+10)/2^{k+1}\right\rfloor
\right)
\]

lies in the three-state set

\[
A=(211,209),\quad B=(209,211),\quad C=(211,211).
\]

Their transitions are A → B, B → A or C, and C → A. Thus both A and B appear
in every three consecutive states. State A gives

\[
s(k+10)<\frac{420}{211},
\]

and state B gives

\[
s(k+10)>\frac{422}{210}=\frac{211}{105}.
\]

These are strictly below and above 2, respectively. Both occur arbitrarily far
out, and ε = 1/106 works in the formal persistence assertion. The proof also
contains the stronger bounded-gap witnesses `bounded_stateA` and `bounded_stateB`.

The prior growth proof uses the binary-prefix invariant
52·2^k ≤ a(k+7) < 53·2^k and an nth-root squeeze.

### A265386 oscillation proof

The existing 48-state certificate checks all 192 possible transitions, then
induction proves bounds at every sufficiently large index. It yields

\[
s(2k+18)<\frac23,\qquad s(2k+17)>3\quad(k\ge0).
\]

The newly packaged persistence corollary takes ε = 1/2 around √2. The formal
limit and these inequalities are unconditional.

## Files and verification

- `statements/oeis-a265385.lean` and `statements/oeis-a265386.lean` are the
  statement submissions. Each retains exactly the one `sorry` required by the
  site's statement-review workflow.
- `proofs/oeis-a265385.lean` and `proofs/oeis-a265386.lean` contain complete
  proofs of the respective imported statements. They end with the site's
  required `OMA.solution : type_of% @...main` declaration.
- `verification/` contains the proof axiom audits and local checker verdicts.
  A local `accepted` verdict means only that the local checker passed; it does
  not mean that an upstream PR was submitted, merged, or credited.
- `review/` records source fidelity, indexing, the interpretation of persistence,
  provenance, and independent mathematical review.
- `verify.sh` stages these four files into the two pinned project checkouts and
  runs the site's unmodified checker. It does not publish anything.

The complete proof endpoints use only `propext`, `Classical.choice`, and
`Quot.sound`. They have no dependency on `sorryAx`, no custom axioms, and no
`native_decide`. The imported statement's admitted body is not used by either
proof.

Pinned verification environment:

| Component | Revision |
| --- | --- |
| Lean | 4.33.1 |
| formal-conjectures | 9097e2f90e66d2f6244209cb1c07f7120d17ec53 |
| Mathlib | 0df444a360eaa60ab8c11dca51a86af692955474 |
| open-math-agents checker | e3a3ffa65b55f913a963a6625588bdceedc6d6d9 |
| Prior proof source in blakestone-x/math | e1b8695d5a785c0b3e978708511327353e8fd127 |

After installing the pinned Lean toolchain and fetching the required Mathlib
cache, run:

```sh
bash verify.sh /path/to/open-math-agents /path/to/formal-conjectures
```

## Submission order

Each problem requires a separate statement PR containing only its corresponding
`statements/<id>.lean` file. Its description should disclose the qualitative
persistence interpretation and link this complete, checked companion proof.
After human review and merge, recheck the proof against the approved statement,
claim the proof target, and submit only `proofs/<id>.lean` in a new PR.

The upstream destination is
[GuillaumeBAUD-coder/open-math-agents](https://github.com/GuillaumeBAUD-coder/open-math-agents).
The local preparation is complete. Creating the required fork is currently
blocked by the absence of an authenticated GitHub browser session and by the
connected GitHub tool's lack of a fork-creation operation.

## Sources and attribution

Stanislav Sykora introduced both sequences and their conjectures on December 7,
2015. The formal definitions follow the executable Gray transforms and the
one-based seeds in the official entries:

- <https://oeis.org/A265385/internal>
- <https://oeis.org/A265386/internal>

The prior proofs are preserved in [A265385](../A265385/README.md) and
[A265386](../A265386/README.md). Site workflow:
<https://lefttosolve.com/join>.

The auxiliary value a(0)=0 makes each sequence a total function. It is unused
by the positive-index recurrence and cannot affect the limits or cofinal
oscillation assertions.
