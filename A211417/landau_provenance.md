# A211417 and Landau's multivariate criterion

Checked 2026-11-27. This is a provenance supplement, not a correction to the verified theorem.

## Primary published result

Jonathan W. Bober, *Factorial ratios, hypergeometric series, and a family of step functions*, Journal of the London Mathematical Society (2) 79(2) (2009), 422--444, DOI https://doi.org/10.1112/jlms/jdn078, arXiv https://arxiv.org/pdf/0709.1977. Theorem 3.1, printed page 7, states Landau's multivariate criterion: a ratio of factorials of homogeneous linear forms with nonnegative integer coefficients is integral for all nonnegative integer inputs if and only if the difference of the corresponding floor sums is nonnegative on the unit cube.

Bober credits Edmund Landau, *Sur les conditions de divisibilité d'un produit de factorielles par un autre*, Nouvelles annales de mathématiques (3) 19 (1900), 344--362: https://www.numdam.org/item/NAM_1900_3_19__344_1/ . The original page also links corrections; Bober's exact modern statement was independently inspected.

## Exact specialization

Put A(n)=(30n)!n!/((15n)!(10n)!(6n)!). For k in {2,3,5} and r>=1 define the two-variable ratio

U(n,t) = (30n)! n! (kn)! ((30r)t)!^r / ((15n)!(10n)!(6n)!(kn+rt)!).

Its Landau function on [0,1]^2 is

F(x,y)=Delta(x)+r floor(30r y)-floor({kx}+ry),
Delta(x)=floor(30x)+floor(x)-floor(15x)-floor(10x)-floor(6x).

The classical 30-step calculation gives Delta(x) in {0,1}. If y>=1/(30r), then r floor(30r y)>=r>=floor({kx}+ry). If y<1/(30r), the last floor is 0 or 1. If it is 1, {kx}>29/30, so for j=1,...,k and d=30/k one has floor(30x)=dj-1. For k=2 these values are 14,29; for k=3 they are 9,19,29; for k=5 they are 5,11,17,23,29. In all cases Delta=1. Consequently F is nonnegative everywhere, including all boundaries.

Landau's theorem makes U(n,t) integral. At t=1 this is

((30r)!)^r A(n) / product_{i=1}^r(kn+i),

which is a **stronger all-consecutive-shifts version** of the Batch10 filtered-product assertion. Multiplying by the omitted factors proves that filtered assertion with exactly the same constant; r=0 is trivial.

## Consequence for attribution

The Batch10 formal proof and all stated endpoints remain valid. Its valuation argument is an independent direct proof of a concrete specialization of classical Landau machinery. The generalized existence assertion, including the supplied factorial constant, is also an elementary consequence of the older published multivariate criterion after the displayed floor check. The source's conjectural label must not be read as evidence that no such earlier general result applied.

This classical specialization was identified independently of the explicit September 19, 2026 ProveIt paper. The latter directly proves the full positive-shift family, so the contribution is now classified as an independent formalization of a previously proved assertion. See [PRIOR_PROOF.md](PRIOR_PROOF.md) for the exact prior proposition and historical source. The classical Landau implication is credited as additional mathematical background.

## Discovery context

The public A211420 project https://github.com/DannyExperiments/a211420-fixed-divisor already explains an analogous two-variable use of Landau in its README and audits/referee_report_1.md. That is how the relevance of the older general criterion was identified. Its A211420 exact lcm constant is a separate, stronger result, and is excluded as a new target.
