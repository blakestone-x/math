# What survives regulator removal: a conditional spectral theorem

Date: 27 November 2026 (America/Chicago).

**Status: complete proofs of the abstract statements below; no proof of the Yang–Mills pressure/orbit hypotheses or of continuum existence. This is an expository research note, not a solution of the Yang–Mills Millennium problem and not a claim of a new spectral theorem.**

This note responds to the screenshot referring to the SU(2) bound
\[
m=\frac{\log(63/32)}{t_0}.
\]
The source is the work of Deep Bhattacharjee and collaborators, [anaxia-research/4Y-M](https://github.com/anaxia-research/4Y-M), inspected at commit [5e50d670bbd52b17a8496489ed9d4cf594a6293e](https://github.com/anaxia-research/4Y-M/tree/5e50d670bbd52b17a8496489ed9d4cf594a6293e). Its README explicitly labels (A) and (P) as hypotheses. Credit for the Yang–Mills reductions and the constant 63/32 belongs to that work. We do not independently certify its full analytic argument here.

## 1. An exact theorem for the reconstructed Hamiltonian

**Theorem.** Let H be a nonnegative self-adjoint operator on a complex Hilbert space, let Ω be a unit vector with HΩ=0, and let D be a dense linear subspace of Ω-perp. Fix t0>0 and 0<q<1. Suppose that, for every v in D and every positive integer n,
\[
0\le \langle v,e^{-nt_0H}v\rangle\le C_v q^n
\tag{1}
\]
for some finite nonnegative C_v independent of n. Then
\[
\operatorname{spec}(H)\subseteq \{0\}\cup[m,\infty),
\quad \ker H=\mathbb C\Omega,
\quad m=-\frac{\log q}{t_0}>0.
\]

**Proof.** Write P for the spectral projection measure of H. The space Ω-perp reduces H. For v in D define the finite positive measure
\[
\mu_v(B)=\langle v,P(B)v\rangle.
\]
For every 0≤r<m the spectral theorem gives
\[
e^{-nt_0r}\mu_v([0,r])
 \le\int_{[0,\infty)}e^{-nt_0E}\,d\mu_v(E)
 \le C_vq^n.
\]
Consequently
\[
0\le\mu_v([0,r])
 \le C_v(qe^{t_0r})^n\longrightarrow0,
\]
because qe^{t0 r}<1. Thus P([0,r])v=0. Taking a countable sequence r increasing to m shows that P([0,m))v=0. Since a spectral projection is bounded and D is dense in Ω-perp, this projection vanishes on all of Ω-perp. On the vacuum it is the identity. Hence P([0,m)) is exactly the projection onto CΩ. Nonnegativity excludes negative spectrum, and the spectral theorem gives both assertions. ∎

Set q=32/63 to obtain the displayed constant. This theorem proves an implication from (1); it does not produce (1) for a Wilson continuum limit.

**One-time version.** It is enough to assume
\[
\langle v,e^{-t_0H}v\rangle\le q\|v\|^2
\quad(v\in D).
\tag{2}
\]
Continuity extends the quadratic-form inequality to Ω-perp. The positive self-adjoint contraction e^{-t0 H} restricted to that space has norm at most q, so its nth power has norm at most q^n, giving (1).

The norm bound in (2) is essential. A bound by an arbitrary vector-dependent constant at just one time gives no gap: every nonnegative H satisfies it with C_v=||v||².

## 2. What a valid limiting passage needs

**Lemma (passage of scalar inequalities).** Suppose F_(a,L)(n) are nonnegative numbers satisfying
\[
F_{a,L}(n)\le C_{a,L}q^n
\]
for every positive integer n. Assume the iterated limits
\[
F(n)=\lim_{L\to\infty}\lim_{a\to0}F_{a,L}(n)
\]
exist, and that 0≤C_(a,L)≤C<∞ uniformly over the parameters used. Then 0≤F(n)≤Cq^n for every n.

**Proof.** For each fixed n take the two limits in the closed interval [0,Cq^n]. ∎

To apply this lemma to the theorem, one must identify these limiting scalars with the **connected** matrix elements of a nonnegative self-adjoint continuum Hamiltonian, on a dense family of vectors in Ω-perp. The required convergence, positivity, density, and vacuum subtraction are assumptions of this application, not conclusions of the scalar lemma. If prefactors depend on n, a uniform constant can be replaced by a finite sequence C_n satisfying limsup C_n^(1/n)≤1; the same spectral proof works.

There is no need to interchange a large-time limit with a regulator limit: first pass the estimate at each fixed n, then let n grow in the limiting theory. Uniform control of the prefactors is nevertheless indispensable.

## 3. Why fixed-time control alone cannot be extended by assertion

Let H on C² have eigenvalues 0 and ε, where 0<ε<m, and vacuum Ω=(1,0). Its connected correlation for v=(0,1) is e^{-εt}; its true gap is ε.

For any finite time horizon T, set C=e^{(m-ε)T}. Then
\[
e^{-\varepsilon t}\le Ce^{-mt}\qquad(0\le t\le T).
\]
Thus even a perfect estimate over finitely many times, with an unrestricted prefactor, does not prove a gap m. An all-time estimate or the uniform quadratic-form contraction (2) is required.

Likewise, consider H_j=diag(0,1/j). Every regulated operator has a strictly positive gap, but H_j converges even in operator norm to the zero operator, whose vacuum is not unique. Positivity of each regulated gap, without a suitable uniform physical lower bound, does not survive the limit.

## 4. The pressure bound already forces spectral suppression

**Proposition.** Let K≥0 have a normalized vacuum and suppose e^{-TK} is trace class for T>0. Set X=log Tr(e^{-TK}). Then X≥0. If X≤x with 0<x<log 2, then the vacuum is unique and
\[
\operatorname{spec}(K)\setminus\{0\}
 \subseteq\left[-\frac1T\log(e^x-1),\infty\right).
\]

**Proof.** The trace includes the vacuum contribution 1. Two linearly independent zero-energy vectors would give trace at least 2, contradicting X<log 2. Since the heat operator is trace class, it is compact; the spectral theorem yields a discrete list of nonzero heat eigenvalues, with multiplicities, and no finite-energy continuous spectrum for K. For each excited eigenvalue E,
\[
1+e^{-TE}\le\operatorname{Tr}(e^{-TK})\le e^x.
\]
Rearrange to obtain the asserted lower bound. ∎

Conversely, in a finite-dimensional system with d excited states, a gap δ gives only
\[
X\le\log(1+d e^{-T\delta}).
\]
A gap by itself does not control the thermal trace uniformly as d grows. This identifies a substantive obstacle in establishing a spacing-uniform pressure bound: one must control the excited-state population as well as their lowest energies.

Here X is the unnormalized log heat trace after setting the vacuum energy to zero. Any application to the source's pressure variable must verify its normalization and geometric factors; this proposition does not identify them by notation alone.

## 5. Outcome and unresolved obligations

The screenshot describes a conditional continuum claim, not an unconditional construction. The following remain unproved in this note:

1. The pressure bound (P), or a sufficient orbit bound (A), along the actual SU(2) asymptotic-freedom trajectory.
2. Existence of a suitable nontrivial continuum Yang–Mills theory with the requisite axioms.
3. The full analytic identification of the source's pressure estimates with the dense-family connected correlation hypotheses above.

The proofs here isolate the spectral endpoint and explain precisely what it would take to use it. They do not discharge these obligations. No Lean compilation or machine certification of this note is claimed.

## References and attribution

- Bhattacharjee et al., [4Y-M README and status table, pinned revision](https://github.com/anaxia-research/4Y-M/blob/5e50d670bbd52b17a8496489ed9d4cf594a6293e/README.md).
- Bhattacharjee et al., [TwoDoublings.lean, pinned revision](https://github.com/anaxia-research/4Y-M/blob/5e50d670bbd52b17a8496489ed9d4cf594a6293e/YangMills/TwoDoublings.lean), including the scalar exponential-vanishing lemma. We inspected the source; we did not rebuild it.
- Bhattacharjee et al., [The SU(2) Yang–Mills Mass Gap from a Single Finite-Volume Bound](https://www.preprints.org/manuscript/202611.1282), for the originating conditional Yang–Mills program.

Prepared with OpenAI ChatGPT for Blake Stone. Elementary examples and spectral arguments are presented for exposition; historical novelty is not asserted.
