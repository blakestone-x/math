# Counting square-zero matrices modulo an integer

Blake Stone · Proof developed with OpenAI Codex

Let $a(n)$ count the $2\times2$ matrices $X$ with entries in $\mathbb Z/n\mathbb Z$ satisfying $X^2=0$. In 2013 Ben Branman conjectured that $a(n)=n^2$ exactly for squarefree $n$. The squarefree direction was already known. In 2015 Robert Israel proposed an exact prime-power formula. We prove both statements. [OEIS A087726](https://oeis.org/A087726)

For odd finite fields, the count of $q^2$ square-zero matrices already appears in Lemma 2 of Acosta-de-Orozco and Gomez-Calderon (1992). The calculation below treats all prime powers, including powers of $2$. [*Matrix powers over finite fields*](https://doi.org/10.1155/S0161171292000991)

**Theorem.** For every $n\ge1$,

$$
a(n)= n^2\prod_{p^k\parallel n}
\left(1+\left\lfloor\frac{k}{2}\right\rfloor(1-p^{-2})\right).
$$

Here $p^k\parallel n$ means that $k$ is the exact exponent of the prime $p$ in $n$. Every factor is at least one and is strictly greater than one exactly when $k\ge2$. This gives Branman's criterion, including $n=1$ by the empty product.

## Count the solutions over a prime power

Fix a prime $p$, put $R_k=\mathbb Z/p^k\mathbb Z$, and let $S_k=a(p^k)$, with $S_0=1$. A matrix over $R_k$ is called primitive here when at least one entry is a unit, or equivalently when its reduction modulo $p$ is nonzero.

Suppose $X$ is primitive and $X^2=0$. Its reduction $\bar X$ is a nonzero square-zero linear map on the two-dimensional space $\mathbb F_p^2$. Its image and kernel are the same line. If $\bar v$ is outside this line, then $\bar X\bar v$ is a nonzero vector on the line. Hence $(\bar v,\bar X\bar v)$ is a basis. Lifting to $R_k$, the determinant of $(v,Xv)$ is a unit, so $(v,Xv)$ is a basis over $R_k$ as well. Exactly $(p^2-p)p^{2(k-1)}$ vectors $v$ work for each primitive $X$, by counting the permitted reductions and their lifts.

Conversely, each ordered basis $(v,w)$ of $R_k^2$ defines a unique primitive square-zero map by $Xv=w$ and $Xw=0$. Thus the number of pairs $(X,v)$ under discussion is exactly the number of ordered bases. It is $(p^2-1)(p^2-p)p^{4(k-1)}$, since a pair of vectors is a basis precisely when its reduction is a basis. Dividing by the number of admissible $v$ for each $X$, we obtain

$$
\#\{\text{primitive square-zero matrices over }R_k\}
=(p^2-1)p^{2k-2}.
$$

For $k=1$, the only remaining matrix is zero, giving $S_1=p^2$. For $k\ge2$, every remaining matrix has the form $X=pY$, with $Y$ uniquely defined modulo $p^{k-1}$. It satisfies $X^2=0$ modulo $p^k$ exactly when $Y^2=0$ modulo $p^{k-2}$. Each such matrix modulo $p^{k-2}$ has $p^4$ lifts modulo $p^{k-1}$, including when $k=2$ and the lower modulus is $1$. This gives

$$
S_k=(p^2-1)p^{2k-2}+p^4S_{k-2}\qquad(k\ge2).
$$

Set $T_k=S_k/p^{2k}$. Then $T_0=T_1=1$, and $T_k=T_{k-2}+1-p^{-2}$. Consequently

$$
S_k=p^{2k}\left(1+\lfloor k/2\rfloor(1-p^{-2})\right).
$$

Using $4\lfloor k/2\rfloor=2k-1+(-1)^k$ gives Israel's formula as stated in A087726. Finally, the Chinese remainder theorem identifies a square-zero matrix modulo $n$ with an independently chosen square-zero matrix at each exact prime-power divisor of $n$. Multiplying the local counts proves the theorem. $\square$

For example, modulo $4$ the primitive count is $12$. Every matrix with all four entries even also squares to zero, giving another $16$ matrices and $a(4)=28$. Modulo $6$, the prime-modulus counts multiply to $4\cdot9=36$.
