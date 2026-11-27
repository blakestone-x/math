# Compositions of twice an integer with range equal to that integer

Research notes for Blake Stone. Proof developed with OpenAI Codex.

Let $a_n$ count ordered compositions of $2n$ whose largest part minus their smallest part is $n$. Write $\varphi=(1+\sqrt5)/2$.

**Theorem.** As $n\to\infty$,

$$
a_n=(n+2)2^{n-3}-\frac{n\varphi^n}{5\varphi^5}+O(\varphi^n).
$$

In particular $a_n\sim n2^{n-3}$, as Václav Kotěšovec conjectured in 2019.

**Proof.** When the minimum is $m$, the maximum $n+m$ exceeds half the total and occurs once. Deleting it leaves two ordered lists of combined weight $n-m$, with every part at least $m$ and some part equal to $m$. Conversely any such pair reconstructs a composition by inserting the maximum between the lists.

Let $B_m(x)=(1-x^m/(1-x))^{-2}$ count ordered pairs of lists with parts at least $m$, including empty lists. Subtracting the pairs missing $m$ and collecting terms gives

$$
\sum_{n\ge1}a_nx^n
=\sum_{m\ge1}x^m(B_m-B_{m+1})
=xB_1-x(1-x)B_2-(1-x)\sum_{m\ge3}x^{m-1}B_m .
$$

Each coefficient involves finitely many summands. The first term has coefficient $(n+2)2^{n-3}$ for $n\ge2$. For the tail, take $\lambda>1$ satisfying $\lambda^3=\lambda^2+1$. Since $\sum_{j\ge3}\lambda^{-j}=1$, induction on the first part bounds the number of single lists of weight $s$ with parts at least three by $\lambda^s$. Thus $[x^s]B_m\le(s+1)\lambda^s$ for $m\ge3$. Summing over $m$ bounds the tail coefficient by $O(n\lambda^n)=o(\varphi^n)$.

Finally

$$
x(1-x)B_2=\frac{x(1-x)^3}{(1-\varphi x)^2(1+x/\varphi)^2}.
$$

At $\rho=1/\varphi$, the partial-fraction coefficient of $(1-\varphi x)^{-2}$ is $\rho(1-\rho)^3/(1+\rho^2)^2=\rho^5/5$. The simple-pole term there contributes $O(\varphi^n)$, and the pole at $-\varphi$ contributes $O(n\varphi^{-n})$. This proves the displayed formula. ∎

Alois P. Heinz's sequence and Kotěšovec's conjecture appear in [OEIS A323111](https://oeis.org/A323111).

[Collected proof PDF, pages 3–4](../notes/compositions-and-divisibility/OEIS-Compositions-and-Divisibility.pdf) · [Source and exact checks](../notes/compositions-and-divisibility/)
