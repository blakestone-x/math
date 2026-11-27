# Compositions with at most one even part and compositions with one run of ones

Research notes for Blake Stone. Proof developed with OpenAI Codex.

**Theorem.** For each $n\ge0$, the number of compositions of $n$ with at most one even part equals the number in which all ones occur in a single consecutive run. Compositions with no ones are allowed, as is the empty composition of zero. Gregory L. Simay proposed this equality in 2018.

**Proof by generating functions.** A composition is an ordered list of positive parts. Let $O=x/(1-x^2)$ and $E=x^2/(1-x^2)$ count a single odd and even part, respectively. An arbitrary list of odd parts has series $A=1/(1-O)$. A composition with one even part splits uniquely at that part, giving the series $A+EA^2$ for the first class.

For the second class, a list with all parts at least two has series $B=(1-x)/(1-x-x^2)$. A nonempty run of ones has series $R=x/(1-x)$. Splitting at the run when it is present gives $B+RB^2$. Substitution gives

$$
A+EA^2 = \frac{(1-x)(1-x^2)}{(1-x-x^2)^2} = B+RB^2.
$$

Equality of coefficients proves the result for every weight. ∎

The collected note also gives explicit bijections from both classes to Jerrold Grossman's words on $1,2,3$ with at most one 3. For example, $(3,4,1,3)$ in the first class and $(2,3,1,3,2)$ in the second both give the word $(2,1,2,3,1,2)$. Simay's 2018 conjecture and Grossman's 2024 interpretation appear in [OEIS A208354](https://oeis.org/A208354).

[Bijection and inverse, PDF page 2](../notes/compositions-and-divisibility/OEIS-Compositions-and-Divisibility.pdf) · [Source and exact checks](../notes/compositions-and-divisibility/)
