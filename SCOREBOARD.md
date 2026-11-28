# Proof fleet scoreboard

The four scoreboard releases contain **50 manuscripts**. This release adds three papers and four contributions to Left to Solve. The first three releases recorded 47 manuscripts across a snapshot of 133 research projects. Project counts refer to the snapshot in which they were recorded. [Open review](https://github.com/blakestone-x/math/pull/1) · [Next proof targets](RESEARCH_PLAN.md)

## Fourth release

| Problem | Result | Manuscript and verification |
|---|---|---|
| Sun's quadratic circular labels over odd extension fields | Queue item 6 is solved for every odd prime power $q>3$ and every quadratic of degree two. The field of three elements is the unique odd-field exception. For squaring at least $(q+1)/2$ successors of zero occur. | [Proof](Sun-polynomial-cycles/odd-fields.pdf) · [Formal moment lemma and finite-field checks](Sun-polynomial-cycles/README.md) |
| Choulet's convolutions and Mathar's recurrences | One parameter identity implies the printed recurrences in 80 OEIS entries. All coefficients and starting indices were checked against the primary sources. Prior proofs of individual cases are credited. | [Proof](Choulet-recurrences/manuscript.pdf) · [All 80 identities and verifier](Choulet-recurrences/README.md) |
| Lagneau's finite prime count, A300984 | The example at $10^7$ omits 937. The corrected count is 39 of 47. The strict majority holds at every decimal cutoff from $10^8$ through $10^{16}$. The assertion for all larger cutoffs remains open. | [Proof and enumeration](A300984/prime-counts.pdf) · [Independent divisor audit](A300984/README.md) · [Lean proof of the geometric-sum subproblem](A300984/DivisorFormulas.lean) |

Left to Solve received four exact Lean statements covering square concatenations, partition prefixes, regular rod polygons and bar tilings. Two proofs and two disproofs passed the site's checker locally and are available for the second submission stage. [Four statement reviews and four checked solutions](notes/left-to-solve-2026-11-27/board-proofs.md)

## Third release

The third release added 19 manuscripts and 67 pages across 14 projects, including nine new project directories. Its 133-project index covered 108 projects from the [upstream snapshot](https://github.com/blakestone-x/math/tree/c92ab48c98acba51cb42ceb73536a7bad251ec2d) and 25 additional projects.

| Problem | Result in this release | Manuscripts and checks |
|---|---|---|
| Sun's quadratic circular permutations, A229827 | For every $n\ge2$, a circle through all residues in which the labels $a_i^2+a_{i+1}$ also exhaust all residues exists exactly when $\gcd(n,6)=1$. This proves the conjecture for every prime $p>3$. The construction also gives quantitative lower bounds for the number of circles. | [Existence and enumeration bounds](Sun-polynomial-cycles/square-circle.pdf) · [Source, exact tests and proof details](Sun-polynomial-cycles/README.md) |
| Sun's two polynomial generalizations | Squaring gives counterexamples over the eight-element field and on a three-element subset of the rationals. The paper also classifies every eligible polynomial function on each field of order through eight. | [Manuscript](Sun-polynomial-cycles/manuscript.pdf) · [Lean certificate for the rational example](Sun-polynomial-cycles/ThreePoint.lean) |
| Circles through a reduced residue system | Sun's conjectured ordering with all directed differences equal to the units, each once, exists for every odd $n>2$. Requiring all sums, or both sums and differences on one circle, is possible exactly when $\gcd(n,6)=1$. The source had already proved the prime-power case for differences. | [Manuscript, verifier and Lean lifting lemmas](Unit-residue-cycles/README.md) |
| Circles through the nonzero squares of a finite field | Exact classification for both quadratic target classes and both edge operations over every odd finite field. For $q>13$ the only failures occur at $q=25$, for square-valued sums and differences. Sun's earlier results on geometric orderings and the positive square-target cases are credited. | [Four failure lists, manuscript and Lean obstruction](Sun-quadratic-residue-circles/README.md) |
| Wiesner's generalized Franel numbers | For every odd prime $p$, $q\ge1$ and even $r\ge2$, the valuation of $\sum_k\binom{p^q-1}k^r$ is $q+v_p(r-1)$. The proposed uniform binary formula fails at $(q,m)=(5,19)$. A corrected formula holds for every $4\le q\le22$ and all $m\ge1$. | [Manuscript, complete row checks and Lean counterexample](Franel-prime-power-rows/README.md) |
| Periodic chess billiards | Almost every direction pair admits a periodic trajectory or a fixed point on every parallelogram. This refutes Hanusa and Mahankali's Conjectures 6.14 and 6.15 and determines the measure after earlier open-density results. The exceptional set has Hausdorff dimension two, and its slices are described by Hecke groups. | [Measure proof](Chess-billiards/manuscript.pdf) · [Dimension proof](Chess-billiards/dimension.pdf) · [Examples and exact checks](Chess-billiards/README.md) |
| Catalan-power Hankel determinants | Cigler's Conjecture 4 holds for every positive power and integer shift. Conjecture 15 holds at every stated parameter. The degree and reciprocity in Conjecture 16 hold with the known degree exception at power one and shift zero. A smaller denominator suffices in the odd case. The paper proves the six displayed low-shift families with the stated normalization corrections and credits earlier determinant evaluations. | [Manuscript, original conjectures and verifier](Catalan-power-Hankel/README.md) |
| Shifted binomial Hankel determinants | Classifies the five identities in Cigler's Conjecture 17. At $m=-1$ one family has a different polynomial for every $k$. For Conjecture 18 it proves both degree predictions, the even leading coefficient, and the corrected odd leading coefficient for all stated parameters. Chern–Shi had already obtained the three positive odd cases of 17 on their valid ranges. | [Proof, earlier specializations and direct determinant checks](Cigler-binomial-Hankel/README.md) |
| Krizek's weighted proper divisors, A245211 | 21 is the only positive fixed point with at most three distinct prime factors, for arbitrary bases and exponents. Every four-prime fixed point has an exponent at most 24, and four equal exponents are impossible. The manuscript also gives a bound in terms of the product of the distinct prime factors for general support size. | [Three-prime manuscript and two computations](A245211/three-primes.md) · [Independent complete verification](A245211/three-prime-independent.md) |
| Krizek's second divisor identity, A245212 | Each progression $mp^e$ with $p\nmid m$ contains at most one solution except for pure powers of two. For a fixed finite prime support, fixed cofactor times one free prime power, or fixed exponent pattern of the odd part, every counterexample can be found by a finite algorithm. Two-prime odd parts with at most 256 divisors are completely excluded. | [Manuscript, exact scope and verifier](A245212/prime-rays.md) |
| Paone–Paone's line-graph signature conjecture | The exact maxima for 10, 11, 12 and 13 independent cycles are 5, 6, 6 and 7 over all graph orders. For every $c\ge2$ the maximum satisfies $f(c)\le\lfloor2c/3\rfloor$, improving the asymptotic upper bound from $5/6$ to $2/3$. The full conjecture is equivalent to $\lim f(c)/c=1/2$. Its upper bound holds at all ranks for simple branch kernels. | [Proof, kernel enumerations and exact graph witnesses](Line-graph-signature/forest-bounds.md) |
| Eulerian matrix powers | For each fixed power $A^r$, the fraction of degree-$n$ roots that are simple and negative tends to one, and their log magnitudes have a Cauchy limit law. All fixed-rank largest roots have explicit asymptotics. For the square, the error in interval counts improves to $O(n\sqrt{\log\log n/\log n})$, both ends are determined, and full real-rootedness is certified through degree 256. Mao and Wang's unrestricted square question remains open. | [Bulk proof](Eulerian-matrix-powers/bulk.pdf) · [Edge proof](Eulerian-matrix-powers/edges.pdf) · [Sharper error for the square](Eulerian-matrix-powers/square-rate.pdf) · [Exact sign certificates](Eulerian-matrix-powers/README.md) |
| Sun's Franel irreducibility conjecture, A000172 | For every odd prime $p$ and $t\ge1$ both indices $(p-1)p^t$ and $(p-1)p^t+1$ are irreducible. For every prime $p\le10^7$ both $2p^t$ and $2p^t+1$ are irreducible for all $t\ge1$. A second manuscript proves every root is simple and negative for every index, and determines the limiting distribution and extreme roots. | [Irreducibility proof](A000172/digits.pdf) · [Zero distribution](A000172/zeros.pdf) · [Checks and prior proofs](A000172/README.md) |
| Shallit's finite integer alphabet, Problem 43 | An explicit word on $\{1,4,7\}$ has a nonzero Hankel determinant at every shift and every odd order, and for every order at a prescribed shift. For any cutoff $R$, three positive symbols at most $48R$ suffice for all orders through $R$ at every shift. The simultaneous all-order, all-shift problem remains open. | [Manuscript, exact valuations and checks](Shallit-Hankel/integer-lifts.md) |
| Sun's coprime-power cycles, A229130 | For exponent $k$ let $r$ count primes $p$ for which $p-1$ divides $k$. At least $3\cdot2^{r-1}-3$ sizes are exceptional. The number of exceptions is unbounded as $k$ varies. The construction gives the three predicted quadratic exceptions. Finiteness for each fixed exponent and the full quadratic classification remain open. | [Manuscript, exact counts and Lean obstructions](Power-coprime-exceptions/README.md) |

## Concurrent work on main

27 project directories arrived between the previous and current upstream snapshots. They enter the project total through the upstream commits. The manuscript counts above cover the fleet's own three releases. [Compare the two upstream snapshots](https://github.com/blakestone-x/math/compare/689c8e59a624ef7802567ca3ce7bbb19cd2b4451...c92ab48c98acba51cb42ceb73536a7bad251ec2d)

| Project | Subject of its manuscript |
|---|---|
| [A016789](A016789/README.md) | Breysens's negabinary XOR identity |
| [A128382](A128382/README.md) | Zeros of iterated divisor sums of Ramanujan's tau function |
| [A128424](A128424/README.md) | A rounded triangle recurrence and the Pisot sequence E(5,7) |
| [A193020](A193020/README.md) | Distinct self-shuffles |
| [A193649](A193649/README.md) | Ten formulas for triangular-array residues |
| [A194469](A194469/README.md) | Which square roots are curbed? |
| [A195825](A195825/README.md) | The positions, lengths and levels of all partition plateaus |
| [A195916](A195916/README.md) | Exact periods in the XOR Pascal triangle |
| [A197170](A197170/README.md) | Every gcd occurs in infinitely many real quadratic fields |
| [A200982](A200982/README.md) | Power sums at prime-power divisors of the Carmichael exponent |
| [A200984](A200984/README.md) | Balanced two-column arrays |
| [A203069](A203069/README.md) | Bounded displacement for greedy composite power-sum permutations |
| [A205573](A205573/README.md) | Three questions on Jeffery's matrix array |
| [A207409](A207409/README.md) | The unique largest remainder on division by smaller primes |
| [A221078](A221078/README.md) | Prime-power congruences for trigonometric power sums |
| [A249303](A249303/README.md) | Factorization of Kimberling's iterated rational functions |
| [A300984](A300984/README.md) | Squarefree sums of squarefree and nonsquarefree divisors |
| [A308355](A308355/README.md) | The exact stable prefix of the partition-length rows |
| [A324017](A324017/README.md) | Two tetration proofs and a counterexample |
| [A377824](A377824/README.md) | The positions of minimum parts in compositions |
| [A380868](A380868/README.md) | Every triangular rectangle count occurs infinitely often |
| [A382632](A382632/README.md) | Which regular polygons can a consecutive rod chain form? |
| [A389524](A389524/README.md) | Divisor row sums and a divisor-count diagonal |
| [A393833](A393833/README.md) | Existence of palindromic proper-divisor residue lists |
| [Bala-product-identities](Bala-product-identities/README.md) | Two exponent conjectures of Peter Bala |
| [Dekking-base-three-halves](Dekking-base-three-halves/README.md) | Factor frequencies and fifth powers in the base-3/2 Thue–Morse words |
| [Rational-base-digit-sums](Rational-base-digit-sums/README.md) | Digit-sum residues on arithmetic progressions in every rational base |

## Second release

The second release added 16 manuscripts to 14 projects. The entries below record the bounds and open cases at that release. [Second release snapshot](https://github.com/blakestone-x/math/tree/5a9d2730dd28ae3031c488960ae2f6cd08a36803)

| Problem | Result | Manuscript and checks |
|---|---|---|
| Chess-rider denominators | Counterexamples to Chaiken, Hanusa and Zaslavsky Conjectures 5.5, 5.8, 5.10 and 6.7. Seven tridents attain denominator 8 against the predicted 7. Ten semiqueens attain 9 against the predicted 8. | [Manuscript and certificates](Rider-denominators/README.md) |
| Ordinary queen denominators | For $q$ queens every denominator through $\exp(q\log\varphi-O(q/\log q))$ occurs. This reaches the exponential rate predicted by Conjecture 6.2. The full Fibonacci endpoint remains open. For configurations built by successive intersections, the maximum is exactly the conjectured Fibonacci number at every size. | [Manuscript and explicit constructions](Queen-denominator-interval/README.md) |
| Mao–Wang’s Delannoy triangle square | The degree-$n$ row has $n$ simple negative roots. The extremal roots approach the endpoints of the sharp interval $[-4-3\sqrt2,-3+2\sqrt2]$. The weighted product theorem has a sharp parameter threshold. The Eulerian-square clause of Conjecture 4.1 is a separate question. | [Manuscript, exact checks and prior partial result](Delannoy-square/README.md) |
| Binomial Eulerian polynomials | Consecutive rows strictly interlace in the ordinary case. For arbitrary positive inversion bounds, strictness through a prefix holds precisely when all those bounds are at least two. Unit bounds give the exact common factor. The paper credits earlier refined-row interlacing and related ordinary results. | [Manuscript and verifier](Binomial-Eulerian-interlacing/README.md) |
| Line-graph signatures | $f(8)=4$ and $f(9)=5$ over all graph orders. For $c\ge8$ one has $f(c)\le c-4$. The limit $\lim f(c)/c$ exists in $[1/2,5/6]$. The next case is $5\le f(10)\le6$. Two enumerations and independent inertia methods checked the extremal cases. | [Manuscript, exact certificate and witnesses](Line-graph-signature/eight-nine.md) |
| Gray-code Fibonacci ratios, A265385 and A265387 | Both recurrences have mean growth 2 for every positive seed pair, and each seed gives at least five accumulation points. For the original seeds, each ratio sequence has at least 280 accumulation points. Every one of its 140 residue classes contains two distinct limits. | [All-seed manuscript and Lean growth theorems](A265387/universal.md) · [Proof for all 140 classes](A265387/phase_paths.pdf) |
| Doubly Gray-transformed Fibonacci ratios, A265386 | Every positive pair of seeds has mean growth $\sqrt2$. Each parity of the consecutive-term ratios has at least three accumulation points, giving at least six in all. | [Manuscript and verifier](A265386/universal.md) |
| Sun’s Franel polynomials | Full irreducibility for every $n\ge2$ at which the odd part of $n$ or $n-1$ is at most 127. For fixed offsets $c\ge0$ from each certified dyadic family, the total degree left outside one irreducible factor is eventually at most $\lfloor c/2\rfloor$. | [Manuscript](A000172/dyadic.pdf) · [Polygon certificate](A000172/dyadic-verification.txt) |
| Franel recurrence and binomial power sums | Proves Conjectures 4.5, 5.4 and 5.6 in the 2014 MSRI-UP report on integral initial values, prime avoidance, and parity. Nonstandard integer seeds have unbounded denominator powers at every odd prime. The power-sum result gives the largest uniform power-of-two modulus at each exponent. | [Manuscript and verifier](Franel-valuation-conjectures/README.md) |
| Binary reverse subtraction | The worst hitting time at widths $2m$ and $2m+1$ is $O(58^{m/20})$, improving the previous base 2 to less than 1.2251. The twenty-pair certificate covers 1,743,392,201 states. | [Manuscript](A338203/shells.pdf) · [Exact table](A338203/shells.txt) · [Low-memory verifier](A338203/shells_independent.cpp) |
| Weighted proper-divisor fixed points, A245211 | Any fixed point with three distinct prime factors has ordered exponents $a\ge b\ge c$ satisfying $4\le c\le25$, $b\le10c+7$ and $a\le(3c+4)b+3c$. For any number of prime factors, no exponent is $-1$ modulo $\ell(\ell-1)$ for any odd prime $\ell$. The global uniqueness of 21 remains open. | [Manuscript and exact checks](A245211/simple-prime.md) |
| Weighted divisor identity, A245212 | Krizek’s powers-of-two classification holds on a set of natural density one and for every positive integer whose odd part is at most $10^8$. Each fixed odd part greater than one has at most one possible dyadic exception. | [Manuscript and verifier](A245212/README.md) |
| Shallit’s fixed-word Hankel problem | For every order $r$ the gcd of the determinants in $\lceil13r/2\rceil$ consecutive shifts is 1. At every shift the orders from $r$ through $\lfloor15r/2\rfloor$ also give gcd 1. These are all-scale results on the individual-nonvanishing conjecture. | [Manuscript](Shallit-Hankel/gcd.pdf) · [Finite context proof](Shallit-Hankel/verify_gcd.py) |
| Shallit’s modular Hankel problem | Conjecture 45 holds for all moduli from 2 through 7. The sharp maximum lengths of words with every contiguous Hankel minor nonzero modulo the given modulus are $2,4,24,22,42,52$, respectively. | [Manuscript](Shallit-Hankel/moduli.pdf) · [Exact counts and witnesses](Shallit-Hankel/moduli-verification.txt) |
| Sigrist’s binary-substring sequence | The partial sums have subexponential growth uniformly over all blocks of $k$ steps. For each $\varepsilon>0$, the indices where the next term exceeds $\varepsilon S_n$ have upper Banach density zero. The number of attained values in $[2^L,2^{L+1})$, divided by $L$, tends to infinity. The permutation conjecture remains open. | [Manuscript and verification](A316994/growth.md) |

## First release

The [first release](https://github.com/blakestone-x/math/tree/c18014b822980b0d6cb9b78fc228e5efda2718c6) added twelve manuscripts in ten new projects. Of their ten main targets, six received full proofs, one received a counterexample, two received partial results, and one had an earlier resolution that the manuscript extended. The table records the results at that release.

| Problem and manuscript | Outcome | What was established | How to check it |
|---|---|---|---|
| [Binary reverse subtraction (PDF)](A338203/manuscript.pdf) | Full termination theorem | Repeated subtraction of a fixed-width binary word’s reversal always reaches a palindrome. For widths $2m,2m+1$, the worst time is between $m$ and $2^{m+1}-2$. Five exact maxima extend the source table through $m=20$. | [Lean proof of termination](A338203/Proof.lean) · [Exact maxima and reproduction commands](A338203/README.md) |
| [Transportation polytopes (PDF)](Transportation-polytopes/manuscript.pdf) | Refuted source conjecture | Alexandersson’s proposed real-rootedness fails at row sums $(12,1,1)$ and column sums $(2,1^{12})$. In this family failure occurs exactly for $m\ge12$, and the number of nonreal zeros grows without bound. | [Lean proof of the polynomial obstruction](Transportation-polytopes/Nonreal.lean) · [Ehrhart enumeration and exact checks](Transportation-polytopes/README.md) |
| [Toroidal semiqueens (PDF)](A342372/manuscript.pdf) | Three numbered conjectures proved | Proves Trump’s (8), (9) and (10) for all admissible board and placement sizes. Gives the whole parity pattern and formulas for up to seven pieces in finite abelian groups. The [period paper](A342372/periods.pdf) proves double-exponential growth of the least toroidal counting period and an exponential interval of ordinary queen vertex denominators. Earlier cyclic formulas through six and earlier full-transversal congruences receive credit. | [Proofs, sources and verifier](A342372/README.md) |
| [Line-graph signatures (PDF)](Line-graph-signature/manuscript.pdf) | Partial result on Paone–Paone Conjecture 5.4 | For $c=2,3,4,5,6,7$ the maxima over connected simple graphs of arbitrary order are $1,2,2,3,3,4$, respectively. For every $c\ge4$ the upper bound improves from $c$ to $c-2$. The [addendum](Line-graph-signature/addendum.pdf) gives an explicit finite search bound for every fixed $c$. | [Mathematical proof and exact inertia checks](Line-graph-signature/README.md) |
| [Gray-code Fibonacci ratios (PDF)](A265387/manuscript.pdf) | Companion conjecture and remaining fluctuation claim proved | A265387 has mean growth 2. The adjacent-term ratios of both A265385 and A265387 have at least **70** distinct accumulation points each. Every subsequence indexed by a single residue modulo 35 fails to converge. The earlier A265385 mean-growth proof is recorded in the baseline. | [Lean scopes, interval table and exact verifier](A265387/README.md) |
| [Signed Deléham triangle (PDF)](A174013/manuscript.pdf) | Three recurrence conjectures proved | Derives Mathar’s recurrences from his published generating function. The minimal polynomial-coefficient recurrence orders are four, four and six. The proposed seven-step recurrence factors through the six-step one. | [Symbolic identities and minimality argument](A174013/README.md) |
| [Checkerboard-avoiding arrays (PDF)](A250956/manuscript.pdf) | Seven strip formulas proved | Gives a transfer matrix for every width, proves the listed strip recurrences, and computes the minimal orders through width 12. Bounds the square-array growth per cell strictly between 1.855317 and 1.880675. | [Exact polynomial and growth verifiers](A250956/README.md) |
| [Sun’s Franel-number polynomials (PDF)](A000172/manuscript.pdf) | Partial result on full irreducibility | Proves irreducibility at $p-2,p-1,p,p+1$ for every prime $p$ in the domain, and at every $2\le n\le2048$. At every index there is a unique factor of degree above half the total, and its share of the degree tends to one. | [Precise theorem and certificate](A000172/README.md) |
| [Bala’s Fibonacci series (PDF)](A295687/manuscript.pdf) | Conjectured evaluation proved | Evaluates the source’s weighted infinite series at every positive index and gives a formula for every positive integer moment at any positive even Fibonacci shift. | [Derivation and source attribution](A295687/README.md) |
| [Binary neighborhood ranks (PDF)](A219525/manuscript.pdf) | Prior result with an extension | Recovers Hardin’s two-dimensional rank from known Lights Out theory and derives output counts and fiber sizes for arbitrary asymmetric boxes, open or periodic boundaries on each axis, and every finite abelian coefficient group. | [Theorem and verification](A219525/README.md) |

All rows refer to research manuscripts posted by this project. A Lean link records the theorem checked by the kernel. Each package describes the role of its computations and gives the originating statement. Historical priority and external acceptance are separate from these checks.

## Further work incorporated from main

Sixteen additional project directories arrived on `main` between `e5967ee` and `689c8e5`. The fleet branch includes those commits and credits these separate results. [Commits in this interval](https://github.com/blakestone-x/math/compare/e5967eeb4e1543514fd4e759827d8b10dddf7332...689c8e59a624ef7802567ca3ce7bbb19cd2b4451)

| Project | Scope recorded in its manuscript |
|---|---|
| [Convex lattice distances](Erdos-132-convex-lattice/README.md) | Counts rare and typical distances in convex regions of the square lattice. Related notes treat affine grids and progression covers as restrictions of Erdős problem 132. |
| [Throwback mixing](Throwback-mixing/README.md) | Gives a necessary and sufficient gcd condition for perfect mixing of increasing queues. |
| [Layman’s sieve](Layman-sieve/README.md) | Proves coordinatewise stabilization at the triangular numbers with an explicit time bound and studies the residue classes. |
| [Morphic discrepancy](Morphic-discrepancy/README.md) | Determines sharp position errors in three binary fixed points and settles the specified inequalities. |
| [Hardin’s constant-stress arrays](Hardin-constant-stress/README.md) | Classifies when rectangles have a common recurrence and establishes 25 table predictions, crediting the five previously proved cases. |
| [A087412](A087412/README.md) | Counts ordered solutions of $x^3+y^3\equiv1\pmod{3^e}$ exactly for $e>1$. |
| [A217280](A217280/README.md) | Classifies the weighted binomial-cube sum modulo five by the digits of its index. |
| [A294413](A294413/README.md) | Proves convergence of the consecutive-term ratio to the golden ratio in the specified complementary recurrence. |
| [A380385](A380385/README.md) | Identifies the Euler-product generating functions of the columns and the exact sequence of row sums. |
| [Arbitrary throwback queues](Throwback-arbitrary/README.md) | Classifies recurrence for arbitrary initial orders and gives limiting label-position distributions. |
| [Kimberling pair replacements](Kimberling-pair-rules/README.md) | Determines the position limits and the valid ranges of the conjectured inequalities for two binary rules. |
| [Rhombus coronas, A233332](A233332/README.md) | Proves order 13 is the least recurrence order for each column, with exact formulas and a symmetry-count correction. |
| [Binary bracelet orbits](A203399/README.md) | Corrects the divisor formula for every table entry and classifies the lengths at which the original rule works on the whole row. |
| [Periodic symmetric functions](Periodic-symmetric-functions/README.md) | Proves the ten proposed symmetric-function formulas and gives the exact recurrence order at every fixed omission count for these periods. |
| [Consecutive-bar tilings](A394981/README.md) | Proves Yane’s factor of four at every odd length from three onward, identifies the exceptional initial pair and gives a recurrence for the full count. |
| [A141344](A141344/README.md) | Derives Mathar’s three-step recurrence and determines the eventual alternating sign beginning at index 17. |

The same commits also strengthened the existing Ducci preperiod, prime-square Erdős–Straus offset, lattice-distance, and complementary-sequence projects. [Ducci distribution](Ducci-preperiod/distribution.md) · [Erdős–Straus offsets](Erdos-Straus-offset/README.md) · [Lattice results](Erdos-132-convex-lattice/README.md) · [Complementary-sequence families](A294532/README.md)

## Earlier additions to main

Three commits from parallel work added **13 projects** after the 52-project audit. Seven arrived in [`4059c10`](https://github.com/blakestone-x/math/commit/4059c10514da03fac9a666b0be177fef77570594). Five more in [`c662a3a`](https://github.com/blakestone-x/math/commit/c662a3ae7284ba5a20ee6ef1c04297638b3f694f) cover 38 OEIS entries, four individual entries and one family of 34, with Lean sources and a [collected manuscript](notes/Math_Proofs_Batch4.pdf). The Fibonacci-weighted periods paper in [`e5967ee`](https://github.com/blakestone-x/math/commit/e5967eeb4e1543514fd4e759827d8b10dddf7332) brought `main` to 65 projects. The table records the scope of those results.

| Project | Result and scope |
|---|---|
| [Modular Ducci preperiods](Ducci-preperiod/README.md) | Establishes the missing matching lower bound in Lewis and Tefft’s even-width conjecture and gives the maximum preperiod at every width and modulus. The proof uses the known cyclic augmentation-ideal nilpotency index. |
| [Erdős problem 132 on a grid](Erdos-132-grid/README.md) | For a complete square grid of $N$ points, the number of distances occurring at most $N^\theta$ times is $N^{\theta+o(1)}$ for fixed $0<\theta\le1$. The question for arbitrary planar configurations stays open. |
| [Prime-square Erdős–Straus offsets](Erdos-Straus-offset/README.md) | Refutes both the proposed bound of 159 and any absolute bound for the least offset on the source project’s Tier 3 primes. Provides a witness with least offset 163. The general Erdős–Straus existence conjecture stays open. |
| [Shallit’s Hankel determinants](Shallit-Hankel/README.md) | Proves nonvanishing for every shift of the infinite word at every order from 1 through 4,096. The conjecture for all orders stays open. |
| [Symmetric Boolean circuits](SymmetricBooleanCircuits/README.md) | Constructs circuits meeting the proposed AND-gate upper bound for every arity and elementary symmetric function. Optimality would require matching lower bounds. |
| [Two-tap cellular automata](Two-tap-automata/README.md) | Characterizes when the period divides the width for arbitrary nonzero weights over a finite field, with coprime stride difference relative to the prime-to-characteristic part $m>2$. The note gives exact periods in the stated cases and credits earlier binary results. |
| [Edit codes](edit-codes/README.md) | Proves $E_4(7r-s,6r-s)=8$ for $r\ge1$ and $0\le s<r$, in particular closing the two listed fixed-length gaps at $(13,11)$ and $(14,12)$. The length-seven base code and repetition identity had prior sources. |
| [A000556 and A000557](A000556/README.md) | Settles both modular-period conjectures of Kinlaw, Morris and Thiagarajan. The first sequence has the full Carmichael period at every modulus. The second has either the full period or half of it, with the exceptional moduli classified. The paper also determines the least periods of A354242 and A354253. |
| [A063956](A063956/README.md) | Proves Yanev’s product identity for the sum of the unitary prime divisors, for every positive pair of integers. |
| [A073642](A073642/README.md) | Proves the squared-valuation identity for weighted binary digits at every index. The power-of-two subsequence rules out the separately proposed natural-log asymptotic constant below $1/2$. |
| [A129453](A129453/README.md) | Dividing the generalized binomial coefficient from the double gcd product by the ordinary binomial coefficient gives an integer square for every $0\le k\le n$. Ma had already established ordinary integrality. |
| [A143132](A143132/README.md) | Proves the final decimal digit repeats $1,6,6,6$ at all positive indices in the binomial transform. |
| [A294532–A294565](A294532/README.md) | One uniform theorem proves convergence of the successive-term ratio to the golden ratio for every complementary pair satisfying the specified equations, across 34 entries. The package gives an explicit error bound. Existence and uniqueness of the pairs are outside its formal scope. |

The update at `c662a3a` also strengthened [A316994](A316994/omitted-values.md). If any integer is omitted, the range has counting function $O_k(X^{\alpha_k})$ for an explicit $\alpha_k<1$. Thus positive upper density of the range or a partial-sum upper bound $S_n\le n^{2+o(1)}$ would settle the remaining permutation conjecture. Its project count stays at one.

The [Palomar branch](https://github.com/blakestone-x/math/tree/5cff8af6bab395d9169ad0907cccb89b85381677) packages [A081732](A081732/README.md) and [A330904](A330904/README.md) in challenge-and-solution format. Both projects are already present in the baseline.

## Repository baseline

At commit [`a80ee14`](https://github.com/blakestone-x/math/tree/a80ee14b88981065189113eace98e1b8fba58c28), the repository contained **52 research projects**. There were 52 `A`-numbered directories. One of them, A232622, and the three `Mathar-*` directories form a single tilings project. Each other `A` directory contributes one project. Companion sequence numbers, individual numbered formulas and the two collected volumes in `notes/` add no projects.

| Main outcome recorded in the manuscript | Projects | How to read the count |
|---|---:|---|
| Theorem | 37 | The manuscript gives an affirmative result or exact formula in the scope stated below. Some derivations use earlier results. |
| Correction or mixed result | 8 | The project both establishes a result and corrects or disproves a substantive assertion. |
| Refutation | 2 | A counterexample or an infinite family disproves the target statement. |
| Prior resolution with extension | 3 | The manuscript identifies an earlier resolution of the source target and gives a further construction, family, or certificate. |
| Open part | 2 | The manuscript explicitly leaves a broader conjecture open and proves a qualifying theorem. |

These are classifications of the archived manuscripts. Publication priority, independent peer review, and agreement by a source author or catalogue require separate evidence. The table uses one outcome per project. Each linked manuscript identifies its original sources and gives its argument.

| Manuscript | Main outcome | What the archived work establishes |
|---|---|---|
| [A068133](A068133/README.md) | Theorem | Every triangular digit sum $T_m$ with $m\ge2$ occurs for infinitely many decimal triangular numbers. The two smaller targets have finite solution sets. |
| [A077754](A077754/README.md) | Theorem | A digit sum $n$ occurs for a zero-free Harshad number of at least two digits exactly when $10\nmid n$ and $n\notin\{1,2,5,11\}$. |
| [A081732](A081732/README.md) | Theorem | One recurrence for canonical ternary numerals implies all nine proposed single-edit identities in their stated range. |
| [A083788](A083788/README.md) | Theorem | Among bounds of the form $S(n)\le n^c$ for the next integer of the same prime signature, the optimal exponent is $\log_2 3$. Exactly the powers of two attain equality. |
| [A085124](A085124/README.md) | Theorem | In base $b$, existence of a multiple whose positive digit product is also divisible by $n$ is equivalent to $b\nmid n$ and all prime factors of $n$ being below $b$. |
| [A085135](A085135/README.md) | Theorem | An application of the unit-equation theorem gives finiteness for any fixed base and finite set of allowed primes. The numeral and just one rotation suffice if there are at least two nonzero digits. An explicit complete list is still a separate task. |
| [A085588](A085588/README.md) | Correction or mixed result | Rule 150 has period equal to width exactly at $2^a(2^k-1)$ for $k\ge3$. The note corrects the first exception to a converse and the direction of a different divisibility observation. Earlier work overlaps the invertible sufficiency direction. |
| [A086004](A086004/README.md) | Theorem | Four successive prime rotate-and-add outputs from a prime are attainable and five are impossible. This resolves the second conjecture in the entry. Wu supplied an attaining example. |
| [A086558](A086558/README.md) | Theorem | For every $n\ge1$, an $n$-digit decimal integer can begin with $n$ and have exactly its prime signature. |
| [A087304](A087304/README.md) | Theorem | Every positive integer in any base has infinitely many multiples preserving its nonzero-digit product, beyond its shifts by powers of the base. |
| [A087324](A087324/README.md) | Correction or mixed result | Infinitely many decimal 9’s-complement pairs share a prime signature. No nonempty all-even signature occurs, disproving occurrence for every signature. |
| [A087325](A087325/README.md) | Theorem | Gives the least 10’s-complement pair starter for every prescribed total prime-factor count, with multiplicity. The proof uses finitely many base cases. |
| [A087339](A087339/README.md) | Theorem | For every prime $p\ge3$, a digit 2 and $p-2$ ones give nonrepunits with prime digit sum and prime digit product plus one. |
| [A087726](A087726/README.md) | Theorem | Gives the exact square-zero $2\times2$ matrix count modulo every $n$. It equals $n^2$ exactly for squarefree $n$. The squarefree direction was known. |
| [A093035](A093035/README.md) | Theorem | Counts all ordered divisor triples whose sum is at most $n$. Its sharp bound of five values per prime signature extends the known odd case. |
| [A094783](A094783/README.md) | Refutation | The divisor record $1680$ maps to $2{,}205{,}403{,}200$ under the least-number-with-$k$-divisors operation. Its nineteenth divisor disproves closure. |
| [A105801 and A181717](A105801/README.md) | Theorem | Every distinct nonnegative seed pair in the Fibonacci–Collatz recurrence stabilizes modulo every power of three at $-1/5$. The equal-seed case is excluded. |
| [A110734 and A110735](A110734/README.md) | Refutation | Every $100^r+1$ for $r\ge1$ gives a zero in both digit-insertion sequences, disproving both positivity claims. |
| [A115047](A115047/README.md) | Correction or mixed result | For $n\ge3$, $n$ divides $12v_n$, and 12 is the least universal multiplier. The prime-index assertion holds for $p\ge5$, with $p=3$ exceptional. |
| [A115770 and A115801](A115770/README.md) | Prior resolution with extension | Earlier finite-state proofs covered the two named carryless equivalences. The manuscript unifies them for all $d\ge2$ through a binary run criterion. |
| [A115772 and A115774](A115772/README.md) | Correction or mixed result | Establishes two strict containments for integer sets defined by ordinary and carryless products. This confirms a proposed inclusion and refutes an equality. |
| [A178811](A178811/README.md) | Prior resolution with extension | Meyerowitz’s 2010 counterexample predates the 2023 claim. A different 80-digit pair gives signature $(3,2,2,2,2)$ and constrains term 499. |
| [A185376 and A185333](A185376/README.md) | Theorem | Counts necklaces with a palindromic cut for any alphabet size, including prescribed color counts. The underlying one-or-two-palindromes classification is credited to Guo, Shallit and Shur. |
| [A208354](A208354/README.md) | Theorem | Gives equal counts and bijections between compositions with at most one even part and those whose ones form at most one run, including the empty composition. |
| [A224341 and A224342](A224341/README.md) | Correction or mixed result | Classifies the unique nonconstant two-cycle of positive-part composition supports and its exact basin. Empty and singleton seeds defeat unrestricted attraction. Five displayed values require correction. |
| [Mathar’s tilings and A232622](Mathar-tilings/README.md) | Correction or mixed result | Indexes derivations for all 44 numbered conjectures in the 2013 paper. Items 3, 9, 12, 23 and 31 involve printed errors or a labeling convention. The index credits Liu’s earlier proof of 6 and earlier work on 9, 15, 17, 18 and 23. [Dominoes](A232622/README.md) · [Narrow strips](Mathar-strips/README.md) · [Rectangular hexominoes](Mathar-hexominoes/README.md) |
| [A238342](A238342/README.md) | Theorem | Establishes the leading asymptotic for every fixed positive multiplicity of the smallest composition part, extending the first ten known columns. |
| [A245211](A245211/README.md) | Open part | The only fixed point with at most two distinct prime factors is 21. The family $p^a q s$ is excluded for distinct primes. A second squarefree fixed point needs at least 203 primes and 12,406 digits. Unrestricted uniqueness is open. |
| [A261781](A261781/README.md) | Theorem | Proves minimal recurrence order $k(k+1)/2$, a second exponential term and strictly increasing spacings tending to $1/\log 2$. Munarini, Poneti and Rinaldi already proved existence of the indicated recurrence. |
| [A265385](A265385/README.md) | Theorem | Proves the Gray–Fibonacci doubling-index root limit of 2 using a stable binary prefix. The source’s observation about adjacent-ratio fluctuations is outside this archived proof. |
| [A265386](A265386/README.md) | Theorem | For the distinct recurrence with Gray transforms inside and outside the sum, the doubling-index root limit is $\sqrt{2}$, and successive ratios alternate above 3 and below $2/3$ from the stated index. |
| [A268135](A268135/README.md) | Prior resolution with extension | Saunders’s theorem implies the infinitude assertion. The manuscript constructs fixed digit sums 86 and 43 for $n$ and $n^2$, with $n$ ending in nine. |
| [A269631](A269631/README.md) | Theorem | The greedy digit-length sequence is a permutation in every integer base, with an explicit bound on the position of each $k\ge2$. |
| [A293929](A293929/README.md) | Theorem | For each fixed base, worst-case and typical minimum numbers of plus signs are asymptotic to $\log_2 L$ for $L$-digit inputs. This proves the infinitude assertion. It bounds the first hard decimal length between $c2^k$ and $Ck^2 2^k$. |
| [A301984](A301984/README.md) | Theorem | Classifies the strict records by binary numerals with at most one zero and gives the first input attaining each record. |
| [A316994](A316994/README.md) | Open part | The greedy binary-substring rule continues indefinitely. Whether it visits every positive integer remains open in this manuscript. |
| [A323111](A323111/README.md) | Theorem | For compositions of $2n$ having range $n$, obtains the leading term $(n+2)2^{n-3}$ and the first exponentially smaller correction. |
| [A330904](A330904/README.md) | Theorem | Four is the maximum run on which binary digit sum equals balanced-ternary digit sum. König supplied the attaining run. |
| [A332520](A332520/README.md) | Theorem | Exactly $2^{s_2(k)}$ positive fixed points have $k+1$ binary digits. The proof uses Sigrist’s earlier observations on equal nonzero blocks and Boolean subcubes. |
| [A334501 and four companion entries](A334501/README.md) | Correction or mixed result | Gives every positive-width full-ring period for five elementary cellular automata from a single occupied cell. A proposed rule-190 recurrence fails at widths 10 and 11. |
| [A334765](A334765/README.md) | Theorem | Three is the maximum run on which binary digit sum equals the negative of balanced-ternary digit sum. König supplied an attaining triple. |
| [A335858](A335858/README.md) | Theorem | Identifies both run-length orderings of binary words, including the permutation giving the right-to-left ordering from the left-to-right one. |
| [A339387](A339387/README.md) | Theorem | Equality of the two residue sums forces squarefreeness. For $n=pq$ with primes $p<q$, it holds exactly when $p$ divides $q+1$. |
| [A344177 and four companion entries](A344177/README.md) | Theorem | A quotient-algebra criterion proves all five recorded polynomial irreducibility comparisons and holds over an arbitrary field under the stated degree and coprimality conditions. |
| [A349802](A349802/README.md) | Theorem | Derives Euler transforms of all columns of the Lyndon-word triangle, fixes binary indexing, and gives an arbitrary-alphabet formula. Howroyd’s earlier program encodes the binary relation. |
| [A354242 and A354253](A354242/README.md) | Theorem | Classical Meixner coefficients give both continued fractions. The modular theorem sharpens an earlier totient bound to the optimal universal period and starting index. |
| [A355255](A355255/README.md) | Correction or mixed result | For cyclic binary differences modulo rotation, proves the power-of-two-width formula. Width 37 begins an infinite counterexample family to the other proposal. Ehrlich earlier computed the labeled period at 37. |
| [A357235, A357216 and A357254](A357235/README.md) | Theorem | With the specified rational side marks and corresponding segments, a triple crossing is possible exactly for 3, 4 and 6 sides. This gives three counts for the other polygons. |
| [A364847](A364847/README.md) | Theorem | Counts similarity classes of $2\times2$ matrices modulo $n$ for each prescribed unit determinant, using the classical local similarity classification. |
| [A366253, A367183 and A367190](A366253/README.md) | Theorem | Gives quartic counts of regions, edges and vertices for all chords between boundary marks. Every crossing involving a chord with an added endpoint is assumed simple. Original diagonals may concur. |
| [A384700](A384700/README.md) | Theorem | Gives the parity-dependent cubic formula for distinct circles through at least three points in a two-row grid, for every width. |
| [A394659](A394659/README.md) | Theorem | Proves eventual degree-$2k$ polynomiality for triangular-grid independent $k$-sets beginning at $n\ge\max(0,k-3)$, and verifies the proposed $k=7$ polynomial. |

### Baseline verification material

Five projects include Lean sources for a main theorem. See [A081732](A081732/Proof.lean), [A105801](A105801/Proof.lean), [A265385](A265385/Limit.lean), [A265386](A265386/Limit.lean) and [A330904](A330904/Proof.lean). Two additional projects use Lean for limited computations. See [A334501 small rings](A334501/SmallRings.lean) and [A355255 residue certificate](A355255/Certificate.lean). The snapshot contains eight PDFs, including the two collected volumes. [Three proof notes](notes/OEIS_Proof_Notes.pdf) · [Compositions and divisibility collection](notes/compositions-and-divisibility/README.md)

All **23** archived Python entry points selected below exited successfully in this audit, including the Mathar symbolic checks and the triangular-grid computation. Their scope ranges from sample checks to exact finite certificates. The Lean coverage in the preceding paragraph comes from source inspection and the archived records. To repeat the Python run, check out the linked baseline in a separate directory and run the following there with Python, NumPy and SymPy installed.

```python
from pathlib import Path
import subprocess
import sys

root = Path.cwd()
scripts = sorted(root.glob('*/verify*.py'))
scripts.append(root / 'notes/compositions-and-divisibility/verify.py')
assert len(scripts) == 23
for script in scripts:
    subprocess.run([sys.executable, '-B', str(script)], cwd=script.parent, check=True)
```
