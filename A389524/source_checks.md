# Source and prior-work checks: A389524

Checked November 26, 2026 (America/Chicago). This is a bounded search record, not an exhaustive priority claim.

## Exact targets

The official OEIS export retains three numbered conjectures. This package proves only:

1. Conjecture 1: the row sum is A000005(n), the number of positive divisors of n.
2. Conjecture 3: T(2n,n) is A049820(n)=n−d(n).

Both theorems cover every positive integer n. The source's Conjecture 2, the weighted row sum giving A274628, is expressly unclaimed. The batch contribution is two assertions in one entry.

## Primary snapshots

The snapshots were read through the official `oeis/oeisdata` repository. Public entry pages and indexed internal pages were also checked.

| File | OEIS revision | Git blob SHA |
|---|---|---|
| [A389524.seq](sources/A389524.seq) | 19, October 22, 2025 | `aada751ae99de30ed9ec5666012b6c7e06321bf5` |
| [A000005.seq](sources/A000005.seq) | 627, September 17, 2026 | `10fd7aab3aa8302e0e4dc66c5337d8d2018b73e5` |
| [A049820.seq](sources/A049820.seq) | 113, January 28, 2026 | `ec0c587868c3d59c864accef81dbad1fedc877bc` |
| [A274628.seq](sources/A274628.seq) | 45, November 5, 2025 | `f0f507930335a96ce317d8720acd822966e40f5e` |

Primary URLs:

- https://oeis.org/A389524
- https://oeis.org/A389524/internal
- https://github.com/oeis/oeisdata/blob/main/seq/A389/A389524.seq
- https://oeis.org/A000005
- https://oeis.org/A049820
- https://oeis.org/A274628

The recursive `triangle` follows the Mathematica source exactly, retaining its first-column rule. The second finite sum is reindexed in Lean without changing its terms. Integer-valued entries preserve negative values. The auxiliary column zero lies outside the source's displayed triangle.

The row-sum target is the cardinality of `Nat.divisors n`; the proof supplies the factor-pair counting bridge. The diagonal target is its integer subtraction from n, matching the defining title of A049820. No independent or alternative sequence is assumed to agree with the source.

## Classical identity and relevant prior mathematics

Uchimura proved the divisor generating identity in 1981:

K. Uchimura, *An identity for the divisor generating function arising from sorting theory*, Journal of Combinatorial Theory, Series A 31 (1981), 131–135. https://doi.org/10.1016/0097-3165(81)90009-1 .

The identity and its partition interpretation are also stated and proved in:

D. M. Bressoud and M. V. Subbarao, *On Uchimura's connection between partitions and the number of divisors*, Canadian Mathematical Bulletin 27 (1984), 143–145. https://doi.org/10.4153/CMB-1984-022-5 . The complete three-page primary paper was read. Its 2018 online publication date is distinct from the original 1984 journal publication.

Further related literature located includes Masanori Ando, *A Combinatorial Proof of an Identity for the Divisor Generating Function*, Electronic Journal of Combinatorics 20(2) (2013), P13, https://doi.org/10.37236/2153 . The q-series identity and its finite analogues are established prior mathematics.

The present Lean file proves the required coefficient form directly by finite polynomial algebra in a nilpotent quotient ring. Its purpose is a complete checked proof of the connection to the 2025 triangle, not a claim to have discovered the classical divisor identity.

## Search scope and exclusions

Both available web search engines were used. Queries included exact identifier searches with `proof`, `theorem`, `Uchimura`, `conjecture 3`, `site:github.com`, and `site:the-omega-institute.github.io`. Searches for Uchimura's identity, finite divisor-generating identities, and the named target sequences identified the classical literature above. The exact-ID results returned the OEIS record and related sequence references; no earlier proof of Conjectures 1 or 3 was located.

The current `blakestone-x/math` README was refreshed before packaging; its blob SHA was `c04124affe5f4858ae8f1255574bed38ca93cc3b`. It contained the prior A380385 result but no A389524 result. A380385's recurrence-to-polynomial proof technique is reused with the new constant term handled explicitly. None of that prior package's two assertions is counted again.

An unchanged conjecture label alone does not establish novelty. The result reported here is a complete proof and formal verification of the two precise assertions after the bounded source and prior-proof checks described above. No exhaustive historical-priority or OEIS acceptance claim is made.
