# Prior-work addendum: complementary Fibonacci limits

November 26, 2026. This supplements the initial source search recorded in this package.

A follow-up search located two public notes uploaded by `bambasene564`:

- [Kimberling Note](https://www.scribd.com/document/1067832042/kimberling-note).
- [Article Style ArXiv Kimberling FR](https://fr.scribd.com/document/1067832340/Article-Style-ArXiv-Kimberling-FR).

Their publication dates have not been established. They discuss related positive-correction complementary Fibonacci equations, including A293358, and a recurrence-normalization approach. This is relevant prior exposition. The earlier limited search should not be read as establishing that this repository originated the general positive-disturbance method. The precise 34-row parameter verification and uniform bound in this package remain the results formally checked here; absolute priority is not claimed.

The first note also states a more general signed-disturbance theorem and claims the negative-correction case A294413. The general theorem as stated is false: the positive constant sequence a(n)=1 satisfies a(n)=a(n−1)+a(n−2)−1 and has a summable disturbance after golden-ratio normalization, but its successive ratios equal 1. Positivity alone does not guarantee positive normalized growth.

This issue does not affect the present A294532–A294565 proof: it proves its disturbance is nonnegative and derives an exponential lower bound before applying the ratio argument. The new [A294413 package](../A294413/README.md) handles the negative-correction equation through a separate counting and growth proof. Both packages explicitly state their formal scope and retain successful kernel checks.

The Lean sources and mathematical conclusions of this package are unchanged. This addendum updates attribution and source-search context.
