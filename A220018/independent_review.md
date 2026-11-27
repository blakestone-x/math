# Independent review: A220018 family

**Result: PASS.** Reviewed November 27, 2026 by the sequence lane, which did not author any theorem in this package. No proof or configuration edits were requested or made.

## Source fidelity

Read all four frozen OEIS entries and compared their definitions and selected conjectures with `Proof.lean`. `C3`, `C7`, `C9`, and `C13` count actual multiplication-orbit quotients modulo `10^n`. The orbit membership theorem identifies group-action orbits with nonnegative powers of the source multiplier. The zero orbit is present; it is not lost by a restriction to units or nonzero residues.

The conclusions preserve the literal coefficients and full ranges: `n > 2` for multipliers 3, 9, and 13, and `n > 3` for multiplier 7. The conclusions lie in the integers, so the displayed subtractions are ordinary subtraction. The underlying definitions do not use the polynomials to be proved. All four immutable-source hashes match the frozen manifest.

One minor prose issue was found and corrected by the author before this final review: A220020 dates Barker's formula April 13, 2013; the other three use April 14. The README and manuscript now say April 13–14. This did not affect proof sources or configuration.

## Mathematical and formal review

Read all six proof modules and the manuscript. The divisor formula follows from literal orbit cardinalities, the equivalence between return exponents and multiplicative order modulo the additive order, and the totient count of elements in each additive-order stratum. The exponent grid is connected to divisors by a proved exhaustive bijection, including the divisor 1.

The order proofs use exact valuation identities for arbitrary exponents. Reviewed the low-exponent cases and the essential exception `v_5(7^4 - 1) = 2`; the other five-adic valuations are 1. The two-adic formulas preserve the threshold behavior of 3, 7, 9, and 13. The Chinese-remainder least-common-multiple step, all finite table entries, and all infinite constant tails are proved. The table summations agree with the manuscript and yield the exact four source polynomials.

There are no admitted steps, `sorry`, custom axioms, or native computation axioms. The supporting order-lifting lemma's valuation hypothesis is discharged in each of its eight applications by the imported proved lifting-the-exponent theorems and exact initial calculations. The endpoint statements have no remaining conjectural hypotheses.

## Fresh build

Ran `python research/batch10/build_package.py output/batch13/A220018 independent`. The harness copied the six proof modules and the three pinned configuration files to a fresh isolated directory, without copying local proof objects. Pinned external dependencies were reused. The default `lake build` compiled every local module and returned exit code 0.

`independent_build.log` records the full build, the four source endpoint axiom reports, the source bridge reports, and SHA-256 hashes. The only endpoint axioms are `propext`, `Classical.choice`, and `Quot.sound`. Every proof/configuration hash in that log was compared with the frozen package after the build and still matches.

## Independent source check

As a separate finite check of interpretation, directly enumerated the permutation cycles on all residues modulo `10^n` for every `n = 1,...,5` and multiplier 3, 7, 9, 13. This algorithm uses neither the divisor formula nor the prime-power-order formulas. All 20 counts matched the corresponding frozen OEIS terms, and every count in a formula's claimed range matched its polynomial. `independent_orbit_check.json` records the results. These finite checks support source fidelity; the unbounded argument is supplied by the Lean proof.

## Provenance and scope

Read the completed source dossier, immutable-source manifest, search receipts, README, and bibliography. They disclose existing divisor-sum programs, polynomial-pattern generators, program-synthesis artifacts, and the substantially more general Zhu–Liu–Wu cyclotomic-coset classification. The package correctly presents the classical methods as prior theory and the four explicit Barker formulas as its selected source assertions. It does not claim a new general classification or worldwide priority.

The recorded exact and semantic search is bounded by returned-result limits and index coverage. This review does not turn those searches into a proof of historical novelty. The package's scope is one mathematical family with four related recorded assertions; auxiliary identities and alternative descriptions are not additional problems.
