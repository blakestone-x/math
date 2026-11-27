# Source and prior-work checks: A380385

## Primary source

The official OEIS entry was read, including its title, comments, example rows, and both Mathematica programs. The entry explicitly points to the first program for the exact recurrence. Its first-column rule is T(n,1)=1 only for n=1, and zero otherwise; the general recurrence applies from column 2 onward. The Lean source follows this program and the displayed data. This distinction is stated in the README.

The official `oeis/oeisdata` file `seq/A380/A380385.seq` was also retrieved. It records revision 20 dated January 25, 2025, 13:54:07. The GitHub blob SHA was `d56997e8a4b51da96ea087378580fcfb4265d9f5`.

Primary links:

- https://oeis.org/A380385
- https://oeis.org/A380385/internal
- https://github.com/oeis/oeisdata/blob/main/seq/A380/A380385.seq
- https://oeis.org/A010815
- https://oeis.org/A231599

## Novelty screening

Both available search engines were used for the exact identifier and combinations with proof, theorem, Euler, Granvik, GitHub, and trureturing. The results located the OEIS statement and database mirrors; no earlier proof of the two selected identifications was located. No claim of global publication priority follows from these bounded searches.

The user repository README was refreshed before selection and again before packaging. At the latter check it had SHA `0964c5a1650676d0fc5742556f3f3481ebfe236f`; neither A380385 nor its +1 sibling A389524 appeared. The candidate was reserved with the coordinating agent to avoid duplicate work.

The known finite Euler product A231599, the infinite Euler product A010815, and the elementary telescoping product identity are credited as prior mathematics. The new target is proving their asserted connection with Granvik's specified recurrence. No separate solve credit is assigned to those classical identities.

## Formal scope

The recursive triangle is defined directly, and strong induction proves its coefficient representation. There is no assumption of the conjectured product formula. Both assertions hold for all source indices, and the degree-stabilization theorem supplies the infinite-product coefficient interpretation without any analytic convergence assumption.
