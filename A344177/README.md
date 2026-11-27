# An irreducibility criterion for two polynomial families

**Blake Stone · Proof developed with OpenAI Codex.**

In 2021 Jianing Song conjectured a relationship between the irreducibility over $\mathbb F_2$ of $x^m+(x^k+1)^R$ and $x^m+x^{kR}+1$. The same conjecture is recorded for five choices of the parameters. We prove it for all the stated parameters by relating two polynomial quotient algebras over an arbitrary field. [A344177](https://oeis.org/A344177) · [A344197](https://oeis.org/A344197) · [A344198](https://oeis.org/A344198) · [A344199](https://oeis.org/A344199) · [A344200](https://oeis.org/A344200)

## A theorem over any field

Let $K$ be a field, let $H\in K[x]$ satisfy $H(0)\ne0$, and let $m,R$ be positive integers with $m>R\deg H$. Define monic polynomials of degree $m$ by

$$
A(y)=y^m-H(y)^R,\qquad B(x)=x^m-H(x^R).
$$

**Theorem.** $A$ is irreducible over $K$ exactly when $B$ is irreducible over $K$ and $\gcd(m,R)=1$. Whenever $\gcd(m,R)=1$, substitution $y\mapsto x^R$ gives a $K$-algebra isomorphism

$$
K[y]/(A)\ \simeq\ K[x]/(B).
$$

**Proof.** If $d=\gcd(m,R)>1$, then $A$ is a difference of $d$-th powers and has the factor $y^{m/d}-H(y)^{R/d}$. Its degree is $m/d$, strictly between $0$ and $m$.

Now suppose $\gcd(m,R)=1$. Denote the classes of $y$ and $x$ in the indicated quotient algebras by $s$ and $t$. The identity $t^m=H(t^R)$ gives

$$
(t^R)^m=H(t^R)^R,
$$

so $s\mapsto t^R$ defines a $K$-algebra homomorphism. As both defining polynomials have nonzero constant term, $s$ and $t$ are units. The equation $H(s)^R=s^m$ makes $H(s)$ a unit as well. Choose integers $a,b$ with $aR+bm=1$. Then

$$
t=(t^R)^a(t^m)^b=(t^R)^aH(t^R)^b
$$

is the image of $s^aH(s)^b$. Negative powers are legitimate because the source elements are units. Thus the map is surjective, and it is an isomorphism since both sides have dimension $m$ over $K$. One quotient is a field if and only if the other is, proving the criterion. $\square$

## Song's conjecture in characteristic two

Set $K=\mathbb F_2$, $R=2^er$ with $r,k$ odd and positive, and $H(y)=y^k+1$, where $m>2^erk$. The minus signs in the theorem become plus signs. Irreducibility of $A$ implies irreducibility of $B$ by the theorem. If $B$ is irreducible, $A$ is reducible exactly when $\gcd(m,R)>1$.

Two restrictions on irreducible $B$ give the further conclusions in Song's entries.

1. If $e>0$ and $m$ is even, then $B$ is the square of $x^{m/2}+x^{kR/2}+1$. Thus $m$ must be odd when $e>0$. In every case, for irreducible $B$, the condition $\gcd(m,R)>1$ is equivalent to $\gcd(m,r)>1$.
2. Let $p$ be any prime dividing $\gcd(m,rk)$. It is odd. For a root $\alpha$ of $B$ and a primitive $p$-th root of unity $\zeta$ in an algebraic closure, $\zeta\alpha$ is also a root since $p$ divides both positive exponents of $B$. The irreducible polynomial $B$ of degree $m$ splits in $\mathbb F_{2^m}$. Thus $\zeta=(\zeta\alpha)/\alpha$ lies in that field, which gives $p\mid 2^m-1$ and $\operatorname{ord}_p(2)\mid m$. The order divides $p-1$ and is coprime to $p$. Since $p\mid m$, we obtain $p\operatorname{ord}_p(2)\mid m$.

These give all of Song's conditions and their stated converse. In particular the discrepancy at $R=3$ occurs, among irreducible $B$, precisely when $3\mid m$ (necessarily $6\mid m$). At $R=5$ it occurs precisely when $5\mid m$ (necessarily $20\mid m$). This also proves that the two descriptions in A344198 with $(r,k)=(3,3)$ and $(9,1)$ give the same set: the trinomial is the same and both greatest-common-divisor conditions reduce to $3\mid m$.
