# Independent statement and mathematical review

Review completed November 27, 2026, by a separate proof-review worker.

The official OEIS internal pages for A265385 and A265386 were fetched and read,
including their sequence definitions, comments, PARI programs, and offsets.
Both proposed statements reproduce those recurrences exactly. Gray(n) is
n XOR floor(n/2), and the seeds use the source's one-based indexing.

The auxiliary a(0)=0 is never used to compute any positive-index recurrence
term. Its effect on the total real expressions is confined to finitely many
indices, irrelevant to the limit and cofinal oscillation assertions. Neither
main theorem adds a hypothesis. The proof witnesses have indices k+10/l+10
for A265385 and 2N+17/18 for A265386. Their denominators are explicitly proved
positive before division inequalities are used.

## New A265385 invariant

Put p=2^k. In state A=(211,209), the sum of the two terms is in
[629p,632p), so division by 4p gives 157 and Gray(157)=211. Thus A→B.
In state B=(209,211), the quotient is 157 or 158, giving Gray values 211 or
209. Thus B→C or A. In state C=(211,211), the quotient is 158 and
Gray(158)=209. Thus C→A.

Both A and B therefore occur within two steps from every state. The resulting
ratios satisfy s(m)<420/211 and s(n)>422/210. Since
420/211 < 2−1/106 and 2+1/106 < 422/210, these prove the stated two-sided
persistence at arbitrarily large indices. The integer and real proof stages
use the same imported sequence definitions. No hidden assumption or substituted
recurrence was found.

## Source interpretation and provenance

The source describes persistence qualitatively. The proposed fixed positive
two-sided separation is a reasonable explicit mathematical interpretation and
is disclosed in both statement docstrings. Human review must accept that
interpretation. The explicit epsilon values 1/106 and 1/2 are supplied by
the proofs and are not attributed to OEIS. The approximate one-percent
description in A265385 is not an exact numerical constraint.

A265385's oscillation extension was developed during this work. Its growth
limit and the A265386 result are ports of Blake Stone's earlier proofs from
repository commit e1b8695d5a785c0b3e978708511327353e8fd127.

## Environment

The required imports compiled together on official Lean 4.33.1 with
formal-conjectures 9097e2f90e66d2f6244209cb1c07f7120d17ec53 and Mathlib
0df444a360eaa60ab8c11dca51a86af692955474. No theorem sources, lint rules,
or checker rules were altered to obtain acceptance.

Sources:

- https://oeis.org/A265385/internal
- https://oeis.org/A265386/internal
