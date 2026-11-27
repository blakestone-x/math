# A uniform AND-gate construction for elementary symmetric Boolean functions

**Blake Stone · Proof developed with OpenAI Codex.**

For $1\le k\le n$, let $\sigma_k^{(n)}$ be the XOR of all squarefree products of $k$ distinct input bits among $n$. Use circuits with binary AND and XOR and unary NOT; the cost is the number of AND gates. Brandão, Çalık, Sönmez Turan and Peralta observed in Appendix A, equation (28), that their computed upper bounds for $n\le25$ fit the formula below. We show how to construct circuits within that bound at every arity. The theorem concerns upper bounds; determining the minimum across all circuits requires a separate lower bound. [Brandão et al., 2019, Appendix A](https://pmc.ncbi.nlm.nih.gov/articles/PMC7047778/#sec7)

**Theorem.** For every $1\le k\le n$, there is a circuit for $\sigma_k^{(n)}$ with at most
$$
B(n,k)=k-1+\sum_{j=1}^{\lfloor\log_2 k\rfloor}\left\lfloor\frac{n-k}{2^j}\right\rfloor
$$
AND gates. The construction uses XOR and AND alone.

## Two elementary observations

On an input of Hamming weight $w$, the value of $\sigma_k^{(n)}$ is $\binom{w}{k}\bmod2$. Over $\mathbb F_2$, the factorization
$$
(1+z)^w=\prod_{i:\,w_i=1}(1+z^{2^i})
$$
shows that the coefficient of $z^k$ is one exactly when all the one-bits of $k$ are present in $w$. Write $k=2\ell+b$ with $b\in\{0,1\}$. For $b=0$ only the bits of $\lfloor w/2\rfloor$ matter. For $b=1$ the output must vanish when $w$ is even. On the odd-weight inputs, deleting any one input bit changes $w$ by at most one and preserves $\lfloor w/2\rfloor$. Using this last observation to factor out the full parity for odd $k$ is also the content of Lemma 12 in Boyar and Peralta. [Boyar and Peralta, 2008, §7.1](https://tsapps.nist.gov/publication/get_pdf.cfm?pub_id=51208)

Given $h$ input wires of integer weight $W$ (their sum), one can construct $\lfloor h/2\rfloor$ carry wires whose integer weight is $\lfloor W/2\rfloor$ using one AND per carry. Replace triples $x,y,z$ of weight-one wires by the weight-one wire $s=x\oplus y\oplus z$, and set aside the carry
$$
c=x\oplus ((x\oplus y)\mathbin{\mathrm{AND}}(x\oplus z)).
$$
The bit $c$ is the majority of the triple and $x+y+z=s+2c$ in ordinary arithmetic. Repeat on the remaining weight-one wires until one or two are left. For a final pair $x,y$, form one more carry $x\mathbin{\mathrm{AND}}y$ and leave their parity as the last weight-one wire. This yields $W=2\sum c_i+(W\bmod2)$ with exactly $\lfloor h/2\rfloor$ carries. The case $h=1$ needs none.

## Recursive circuit and gate count

For $k=1$, output parity at zero AND cost. For $k\ge2$, set $u=\lfloor(n-b)/2\rfloor$. Compress the first $n-b$ wires as just described, costing $u$ AND gates, and feed the $u$ carry wires into a recursively constructed circuit for $\sigma_{\ell}^{(u)}$. The hypothesis $n\ge 2\ell+b$ ensures $u\ge\ell\ge1$.

If $b=0$, that recursive result is the desired output. If $b=1$, AND it with the parity of all $n$ inputs. It is then correct at even weight because the parity factor is zero. At odd weight the carry wires have total weight $\lfloor w/2\rfloor$, by the deletion observation, so the recursive circuit tests exactly the remaining one-bits of $k$.

Each step costs $u+b$ AND gates in addition to the recursive circuit. The closed formula obeys this recurrence. In fact,
$$
u-\ell=\left\lfloor\frac{n-k}{2}\right\rfloor,
\qquad
B(n,2\ell+b)=u+b+B(u,\ell).
$$
The first term of the sum for $B(n,k)$ is $u-\ell$, while every later term gives the matching term for $B(u,\ell)$ by repeated integer division. The base value is $B(n,1)=0$. Induction on $k$ proves the theorem. ∎

For instance, at $(n,k)=(26,9)$ the first stage drops one input, forms twelve carry wires and gates the result by parity. A circuit for $(12,4)$ adds six gates and then a circuit for $(6,2)$ adds three. The final $(3,1)$ stage is an XOR, giving $13+6+3=22$ AND gates.

The formula applies separately to each elementary symmetric function. General symmetric functions can be XORs of many such functions, and paying for separately constructed circuits does not determine the largest minimum gate count for all symmetric functions on 22 inputs. NIST asks whether that maximum is 21 or 22. [NIST Circuit Complexity project](https://csrc.nist.gov/projects/circuit-complexity)

The accompanying Python implementation constructs the straight-line gate list. Its tests compare the actual gate counts to the formula, and evaluate complete truth tables against binomial parity for small arities. [Circuit constructor and verifier](verify.py)
