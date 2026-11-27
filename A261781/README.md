# Minimal recurrences and growth constants for marked compositions

Research notes for Blake Stone. Proof developed with OpenAI Codex.

Let $T(n,k)$ count compositions of $n$ in which each part is marked by a weakly increasing word of that part's length on $k$ ordered letters. Every letter must appear somewhere. This is the sequence of matrix compositions with $k$ nonzero rows in Table 2 of Munarini, Poneti, and Rinaldi (2009).

Václav Kotěšovec recorded two conjectures in 2017 concerning the recurrence order and the spacing of the exponential growth constants. **The existence of the recurrence of the stated order was already Proposition 25 of the 2009 paper.** The argument below also proves minimality, identifies the second exponential term, and shows that the spacings strictly increase to the proposed limit.

## The exact order

For fixed $k\ge1$, the minimal order of an eventual homogeneous linear recurrence with constant coefficients for $T(n,k)$ is $k(k+1)/2$.

**Proof.** Given $j$ available letters, one nonempty marked part has generating function $(1-x)^{-j}-1$, since each letter has an arbitrary multiplicity. A list of such parts has series

$$
F_j(x)=\frac{(1-x)^j}{2(1-x)^j-1}.
$$

Here $F_0=1$. Inclusion-exclusion on the letters that never appear gives the published generating function

$$
G_k(x)=\sum_{n\ge0}T(n,k)x^n
=\sum_{j=0}^k(-1)^{k-j}\binom{k}{j}F_j(x).
$$

For $j\ge1$, the denominator $Q_j(x)=2(1-x)^j-1$ has $j$ simple roots. At each root the numerator is $1/2$, so each is a genuine pole of $F_j$. A root of $Q_j$ satisfies $|1-x|=2^{-1/j}$. These radii are distinct for different $j$, so no other summand can cancel the pole. The reduced denominator of $G_k$ is exactly $\prod_{j=1}^k Q_j(x)$, with constant coefficient 1. Its degree is $1+2+\cdots+k$. A recurrence of order $h$ would yield a denominator of degree at most $h$ on multiplying the series by the recurrence polynomial. Conversely the reduced denominator gives a recurrence of its degree. ∎

## Two leading terms

Let $r_j=1-2^{-1/j}$, $d_j=1/r_j$ and $c_j=1/(2j(2^{1/j}-1))$. For each fixed $k\ge1$ we have $T(n,k)\sim c_k d_k^n$. More precisely, for $k\ge2$ there is a constant $0<\theta_k<d_{k-1}$ for which

$$
T(n,k)=c_kd_k^n-kc_{k-1}d_{k-1}^n+O(\theta_k^n).
$$

**Proof.** The roots of $Q_j$ are $1-\alpha_j\zeta$ with $\alpha_j=2^{-1/j}$ and $\zeta^j=1$. The nearest to zero is $r_j$, uniquely. As $F_j=1/2+1/(2Q_j)$ and $Q'_j(r_j)=-j/\alpha_j$, its partial fraction at $r_j$ is $c_j/(1-x/r_j)$. The radii $r_j$ decrease strictly with $j$, so $r_k$ is the unique nearest pole of $G_k$.

The next nearest pole is $r_{k-1}$. For $j<k$ the preceding radius bound suffices. For any $\zeta^k=1$ with $\zeta\ne1$ we have

$$
|1-\alpha_k\zeta|\ \ge\ 2\sqrt{\alpha_k}\sin(\pi/k)
\ \ge\ 4\sqrt{\alpha_k}/k \ >\ 2/k.
$$

The middle inequality uses $\sin t\ge 2t/\pi$ on $[0,\pi/2]$. Meanwhile $r_{k-1}<(\log 2)/(k-1)<2/k$. All remaining pole moduli therefore exceed $r_{k-1}$. Every pole is simple, and inclusion-exclusion gives coefficient $-k$ to $F_{k-1}$. Partial fractions give the expansion. ∎

## Why the spacings increase

Set $L=\log 2$ and interpolate $d_k$ by $d(x)=(1-e^{-L/x})^{-1}$ for real $x>0$. With $u=L/(2x)$, differentiation gives

$$
d'(x)=\frac{1}{L}\left(\frac{u}{\sinh u}\right)^2.
$$

For $u>0$, the function $u/\sinh u$ decreases strictly with $u$. Indeed the derivative has numerator $\sinh u-u\cosh u$, which starts at zero and has derivative $-u\sinh u<0$. Since $u$ decreases to zero as $x$ increases, $d'(x)$ increases strictly to $1/L$. Integrating over $[k,k+1]$ proves

$$
d_{k+1}-d_k\ \nearrow\ \frac1{\log 2}.
$$

**Sources.** The conjectures and numerical constants appear in [OEIS A261781](https://oeis.org/A261781). See E. Munarini, M. Poneti, and S. Rinaldi, [Matrix compositions](https://cs.uwaterloo.ca/journals/JIS/VOL12/Rinaldi/rinaldi.pdf), Journal of Integer Sequences 12 (2009), Article 09.4.8. Propositions 12–13 give the poles and leading term for unrestricted rows. Propositions 24–25 give the generating function and recurrence for nonzero rows.

[Exact coefficient and recurrence checks](verify.py)

Run `python3 verify.py` in this directory to check the first eight column recurrences through weight 100 and compare the first four columns with a direct enumeration of words and cuts through weight 7.
