# Prime signatures of decimal 9's complements

**Blake Stone** · Proof developed with OpenAI Astra 6.2.

The prime signature of an integer is the multiset of exponents in its prime factorization. For a positive integer $n$ of decimal length $d$, write $C(n)=10^d-1-n$. In 2003 Amarnath Murthy conjectured both that infinitely many $n$ share their prime signature with $C(n)$ and that every prime signature occurs this way. We prove the first conjecture and disprove the second. [OEIS A087324](https://oeis.org/A087324)

## Infinitely many complementary pairs

Let $R_d=(10^d-1)/9$, a string of $d$ ones. The numbers $2R_d$ and $7R_d$ are strings of twos and sevens, respectively. They are each other's 9's complements. Whenever $R_d$ is coprime to $14$, multiplying it by $2$ or by $7$ appends one exponent equal to $1$ to its prime signature.

This works for every odd $d$. The repunit is odd. The multiplicative order of $10$ modulo $7$ is $6$, since $10\equiv3$, $3^2\equiv2$, and $3^3\equiv-1\pmod7$. If $7$ divided $R_d$, then $10^d\equiv1\pmod7$, forcing $6\mid d$. Thus every odd length supplies a complementary pair. For instance, $222=2\cdot3\cdot37$ and $777=7\cdot3\cdot37$.

Indeed, even the number of **distinct prime factors** in these examples is unbounded. Set $d=3^j$ and use

$$
R_{3d}=R_d(10^{2d}+10^d+1).
$$

The factor in parentheses is $3$ modulo $9$ and greater than $3$, so it has a prime factor other than $3$. Modulo $R_d$ the parenthesis equals $3$, so that new prime does not divide $R_d$. Iterating gives signatures of unbounded length.

## Why some signatures never occur

If every exponent of a nonempty prime signature is even, every integer with that signature is a square. Two positive squares cannot sum to $10^d-1$. For $d\ge2$ this sum is $3$ modulo $4$, whereas squares are $0$ or $1$ modulo $4$. For $d=1$, no two positive squares sum to $9$. In particular the prime-square signature $(2)$ never occurs.

These statements concern 9's complements. Robert Israel recorded a separate obstruction for prime powers with even exponent in the companion 10's-complement sequence. [OEIS A087325](https://oeis.org/A087325)
