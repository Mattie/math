# How close can a fraction get?

Here's the number we're studying, rounded to 20 decimal places:

$$
x=\frac{\log(3+2\sqrt2)}{\sqrt2}\approx1.24645048028046102679.
$$

The logarithm is the natural logarithm, the one whose derivative is $1/t$. These fractions give us a few ways to approach $x$:

| Fraction | Decimal value (rounded) | Absolute error (approximately) |
|---|---:|---:|
| $5/4$ | 1.250000000000 | 0.003549519720 |
| $86/69$ | 1.246376811594 | 0.000073668686 |
| $263/211$ | 1.246445497630 | 0.000004982650 |
| $1229/986$ | 1.246450304260 | 0.000000176021 |

You can already get quite close with a denominator under 1,000. But a table can't tell us what happens for all the fractions we haven't tried. Even a million more digits wouldn't do that.

Ryan Matthew Casper's [paper](../paper.pdf), dated 7 October 2026, proves that this number has *irrationality exponent 2*. We'll unpack that phrase, then look at the arithmetic trick behind the proof. The [manuscript](../build/manuscript.md) has the full argument.

## What are we measuring?

For a fraction $p/q$ with a positive denominator, its error is $|x-p/q|$. A bigger denominator gives you more choices, so we should judge the error relative to $q$.

One useful target is

$$
0<|x-p/q|<\frac1{q^2}.
$$

Our last fraction meets it: its error is about $0.000000176$, while $1/986^2$ is about $0.00000103$. A theorem of Dirichlet says that every irrational number has infinitely many reduced fractions meeting this squared-denominator target.

Now make the target harder by replacing 2 with 3. At denominator 1,000, you're asking for an error below one billionth instead of one millionth. Or try 2.01; that's a smaller improvement, but it still gets more demanding as the denominator grows.

The paper proves that for every fixed positive $\varepsilon$, there is a threshold beyond which every fraction satisfies

$$
\left|x-\frac pq\right|\ge\frac1{q^{2+\varepsilon}}.
$$

You choose $\varepsilon$ first. The threshold can depend on that choice, and the paper doesn't give a numerical recipe for finding it. Exceptional fractions below the threshold are allowed.

So exponent 2 says we can keep meeting the target at 2, but can't keep beating any fixed exponent above 2. It doesn't say every good fraction has error exactly $1/q^2$. There is still plenty of room for some fractions to be better than others.

## Why this particular number?

There's a calculus way to write it:

$$
x=\int_0^1\frac{dt}{1-t^2/2}.
$$

For example, differentiating

$$
\frac1{\sqrt2}\log\frac{\sqrt2+t}{\sqrt2-t}
$$

gives the integrand. At $t=1$, the fraction inside the logarithm is $3+2\sqrt2$.

The useful arithmetic comes from changing the sign of the square root:

$$
(3+2\sqrt2)(3-2\sqrt2)=1.
$$

One number is about $5.828$; its partner is about $0.172$. Their product is exactly 1. If you raise the small one to larger powers, it gets as close to zero as you like, while the other one gets correspondingly large.

That's an obstacle for our proof. Numbers involving integer multiples of $\sqrt2$ can be extremely small without being zero. We can't treat them like integers.

But their paired products behave better. For integers $a,b$,

$$
(a+b\sqrt2)(a-b\sqrt2)=a^2-2b^2.
$$

Unless $a=b=0$, the result is a nonzero integer. Its absolute value is at least 1. The two factors can trade size, but they can't both become tiny.

## How does that stop overly good fractions?

Suppose, for a contradiction, we had fractions that kept beating one fixed exponent above 2. The proof chooses several of them and builds a square matrix. Its determinant is a number calculated from the entries; for a two-by-two matrix, the formula is $ad-bc$.

After clearing denominators, our determinant has the form $a+b\sqrt2$. A deep interpolation theorem lets us choose a determinant that isn't zero. Taylor expansions and the exceptionally good fractions then give bounds making it small.

Small isn't enough, as $3-2\sqrt2$ just demonstrated. We also need its partner $a-b\sqrt2$ to be small, with enough room to pay for all the denominator factors. The proof gets that second estimate from the same matrix, with every occurrence of the square root changed consistently. We don't pick another convenient matrix and hope its determinant is the partner (it probably wouldn't be).

The resulting product would be a nonzero integer with absolute value below 1. That's the contradiction. Making the estimates strong enough for *every* exponent above 2 takes most of the paper.

The same eventual bound also proves that $x$ is irrational: if it were a fraction, we could keep multiplying its numerator and denominator by the same integer, giving exact answers with arbitrarily large denominators. Zero error would violate the bound. Dirichlet's theorem then supplies the approximations at exponent 2.

## Where does the work come from?

OpenAI's [paper and library on the irrationality exponent of $\pi$](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026) supplied the interpolation and determinant method. Casper's preceding [rational-logarithm paper](../../The-irrationality-exponent-of-positive-rational-logarithms-is-2-October-7-2026/README.md) and [imaginary-quadratic paper](../../The-irrationality-exponent-of-arctan-sqrt2-over-sqrt2-is-2-October-7-2026/README.md) adapted that framework. Here the extra problem is keeping both real partners under control.

This sort of normalized logarithm already appears in [Bashmakova and Zolotukhina's 2017 work](https://www.mathnet.ru/eng/cheb531). The manuscript explains the connection; we don't claim to have identified the strongest previous bound for this particular value.

The division by $\sqrt2$ is part of the result. Multiplying by an irrational number doesn't generally preserve how well fractions approximate a number, so this paper doesn't also settle the unscaled logarithm. If you'd like to see why the division fits the proof, the [bachelor's version](ELIBS.md) follows the two exponential identities more closely.

*Casper initiated and directed the investigation. OpenAI coding agents contributed substantially to the mathematical adaptation, formal proof, verification work, and exposition. The paper credits OpenAI's inherited framework and Mathlib; the [verification record](../lean/VERIFICATION.md) describes the checks. These checks are not external human peer review.*
