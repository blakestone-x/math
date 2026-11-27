# A265386 proof audit

Audit date: 2026-11-26.

## Result checked

The package proves the exact mean-growth assertion recorded for [OEIS A265386](https://oeis.org/A265386):

$$
\lim_{n\to\infty}\left(\frac{a(2n)}{a(n)}\right)^{1/n}=\sqrt 2,
$$

where $a(1)=a(2)=1$, $G(m)=m\mathbin{\mathrm{xor}}\lfloor m/2\rfloor$, and
$a(n)=G(G(a(n-1))+G(a(n-2)))$ for $n\ge3$.

The final Lean theorem is `A265386.growth_rate_limit`. It has no hypotheses. Its expression uses real division and real powers, with the exponent `1 / (n : ℝ)`. The auxiliary value `a 0 = 0` is never used by the recurrence for positive indices and does not affect the limit.

The package also proves explicit persistent fluctuations: for every integer $k\ge0$,

$$
3a(2k+16)<a(2k+17),\qquad
3a(2k+18)<2a(2k+17).
$$

All relevant terms are positive. Thus every odd-indexed adjacent ratio from index 17 exceeds 3, and every even-indexed adjacent ratio from index 18 is below $2/3$. These are the precise inequalities formalized by `A265386.adjacent_oscillation`.

## Mathematical review

The invariant and the link to the original recurrence were checked directly.

1. **Binary prefixes.** `gray_div_pow` proves
   $\lfloor G(s)/2^k\rfloor=G(\lfloor s/2^k\rfloor)$ for every natural $s,k$.
2. **Carries.** Dividing a sum by $2^k$ gives the sum of the two quotients plus a carry in $\{0,1\}$. The proof establishes this fact for arbitrary inputs, rather than inferring it from sampled terms.
3. **Finite certificate.** The state list has 48 distinct pairs. Starting from $(158,510)=(a(16),a(17))$, every state remains in the list under all four choices of the two carries. All 192 transitions were checked by a separate implementation. The Lean theorem `certificate_closed` independently proves the full finite statement by `decide`.
4. **Induction.** `prefix_state` proves for every $k\ge0$ that
   $(\lfloor a(2k+16)/2^k\rfloor,\lfloor a(2k+17)/2^k\rfloor)$ belongs to that list. The carries are allowed to vary arbitrarily; no independence or recurrence assumption about their values is needed. The induction connects both new terms to the exact nested-Gray recurrence.
5. **Bounds.** The certificate gives
   $136\,2^k\le a(2k+16)<160\,2^k$ and
   $489\,2^k\le a(2k+17)<512\,2^k$.
   These imply $2^n\le4a(n)^2$ and $a(n)^2<2\cdot2^n$ for every $n\ge16$.
6. **Limit.** The analytic proof obtains
   $$
   \tfrac14(\sqrt2)^n\le\frac{a(2n)}{a(n)}\le4(\sqrt2)^n
   \quad(n\ge16).
   $$
   Taking positive real nth roots and applying the squeeze theorem proves the stated limit. The generic analytic lemma's positivity and bound hypotheses are discharged using proved theorems about this exact sequence.

A separate direct recurrence calculation through index 1000 was used as a consistency check. The proof itself applies to every natural index by induction; it does not extrapolate from that calculation.

## Formal verification

The final packaged files were copied unchanged to a separate build directory. `Proof.olean` was rebuilt there, placed first on the import path, and then used to rebuild `Limit.olean`. Both compilations exited with status 0. This avoids importing a stale module with the same filename. The actual package also passed a fresh `lake build`; see `verification.txt`. The separate compilation output is preserved in `audit-verification.txt`.

Verified environment:

- Lean 4.19.0, compiler commit `6caaee842e94`.
- Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`, pinned in `lakefile.lean`.

Source inspection found no `sorry`, `admit`, custom axiom declarations, `native_decide`, unsafe declarations, or replacement implementations. The finite checks use ordinary `decide`, with proof terms checked by Lean. The arithmetic and analytic tactics likewise produce kernel-checked proofs.

Lean reports exactly the ordinary foundational axioms `[propext, Classical.choice, Quot.sound]` for all six printed results: `prefix_state`, `parity_bounds`, `positive`, `adjacent_oscillation`, `squared_bounds`, and `growth_rate_limit`. No `sorryAx` or additional axiom appears.

## Public status and earlier-work search

The [official internal entry](https://oeis.org/A265386/internal), saved during this work, still labels the mean-growth statement a conjecture. Its entry revision is `#16 Jan 16 2016 18:08:45`; it attributes the sequence to Stanislav Sykora on December 7, 2015. Its listed links are the sequence's table and general Fibonacci and Gray-code background, with no proof linked.

Searches on 2026-11-26 covered the exact sequence identifier with proof, theorem, limit, and formalization terms, as well as the nested Gray recurrence and Gray/Fibonacci growth descriptions. The following public sources were also inspected for the identifier and equivalent results:

- [trureturing's resolved-conjecture index](https://www.trureturing.org/conjectures).
- [Fabian Arevalo's mathematics index](https://fabianarevalo.com/math).
- [Eppie's OEIS proof repository](https://github.com/Eppie/oeis-proofs).

No earlier proof of this assertion was found in those searches. This supports describing the result as a proof of a conjecture still publicly listed in OEIS. It does not establish exhaustive priority over unpublished work or material absent from the searched sources.

## Exact reviewed files

| File | Lines | SHA-256 |
| --- | ---: | --- |
| `Proof.lean` | 187 | `60325d9751e142cd53c3135bdf1621aa1d964d98e2c15c27bc94b222bdd89e68` |
| `Limit.lean` | 166 | `2e3d16cb21d9fd70dfffbbd7f20de0d4fd6beaffe10f316194a0a2bccf52baf8` |

The certificate is embedded completely in `Proof.lean`; correctness does not depend on trusting its discovery script or a separate JSON file.
