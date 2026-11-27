# Source and prior-work checks: A294413

Checked November 26, 2026. This is a bounded search record, not an assertion of exhaustive priority.

## Defining source

- https://oeis.org/A294413
- https://oeis.org/A294413/internal
- https://github.com/oeis/oeisdata/blob/main/seq/A294/A294413.seq

The official entry and its export were read. The export is revision 9, November 1, 2017, and the original author is Clark Kimberling, October 31, 2017. The title, initial values, a-data, and Mathematica program match the formal `Solution`. The source's complement example erroneously includes 6, which is already a(2); this is documented in the README and independent audit. No condition is taken from that inconsistent example.

The signed recurrence is shifted from source index n to formal index n+2 and interpreted over the integers. Both sequences are increasing positive complements. The desired ratio limit is stated explicitly as a conjecture in the retrieved entry.

## Prior work reviewed

1. Clark Kimberling and Peter J. C. Moses, *Linear Complementary Equations and Systems*, Fibonacci Quarterly 57(5) (2019), 96–110. https://www.fq.math.ca/Papers1/57-5/kimberling-moses.pdf . Theorem 2.1 requires existence of the ratio limit in condition (ii) and a positive disturbance in condition (iii); it does not supply the present negative-disturbance convergence theorem.
2. *Kimberling Note*, publicly uploaded by `bambasene564`; date not established. https://www.scribd.com/document/1067832042/kimberling-note . The note explicitly claims A294413. Its stated general signed-disturbance theorem is false, as shown by the constant-sequence counterexample in the README. The proof here independently establishes the exponential lower bound needed in this case.
3. Related French-language sketch concerning A293358: https://fr.scribd.com/document/1067832340/Article-Style-ArXiv-Kimberling-FR . This and the positive-disturbance discussion in the preceding note are relevant prior arguments, not new results claimed in this package.

Exact-identifier searches, complementary-recurrence and golden-ratio searches, the cited journal paper, and public OEIS proof collections were checked. The discovered earlier attempt is acknowledged explicitly. No earlier complete valid proof of the exact negative-correction assertion was located in this search.

The mathematical contribution of this package is the derived counting/growth argument for A294413 and its formal completion, including a quantitative ratio bound. It is not a claim that recurrence contraction, Euler's golden-ratio identity, or the positive-error method is new. The package is one result about one OEIS entry; related positive-correction entries are not counted again.

## Verification scope

The theorem quantifies over every pair satisfying the source's complementary-sequence conditions. Growth and convergence are conclusions. A separate formal construction or uniqueness theorem is not included. Exact source and package hashes are listed in [SHA256SUMS.txt](SHA256SUMS.txt); the final Lean files have independent audit hashes as well.
