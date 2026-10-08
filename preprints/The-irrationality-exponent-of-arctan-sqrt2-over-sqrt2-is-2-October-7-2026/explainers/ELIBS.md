# What does exponent 2 tell us about this arctangent?

The target is a real number, with the angle measured in radians. Rounded to 20 decimal places, it's

$$
y=\frac{\arctan\sqrt2}{\sqrt2}\approx0.67551085885603996302.
$$

Here are four rational approximations:

| Fraction | Decimal value (rounded) | Absolute error (approximately) |
|---|---:|---:|
| $169/250$ | 0.676000000000 | 0.000489141144 |
| $25/37$ | 0.675675675676 | 0.000164816820 |
| $102/151$ | 0.675496688742 | 0.000014170114 |
| $331/490$ | 0.675510204082 | 0.000000654774 |

Rounding to three decimal places produces $169/250$. But $25/37$ gets closer with a much smaller denominator, and $331/490$ gains quite a bit more accuracy without an enormous one. We're interested in how much accuracy the denominator can buy us.

The decimals in the table are rounded, and none of the fractions equals $y$. The proof of irrationality comes from an argument about all denominators, not from inspecting a finite decimal expansion.

Ryan Matthew Casper's [paper](../paper.pdf), dated 7 October 2026, proves $\mu(y)=2$. The [manuscript](../build/manuscript.md) contains the full argument; this explanation uses algebra, calculus, and complex numbers to get at its structure.

## How do we compare fractions fairly?

For an irrational number $z$, its *irrationality exponent* is the supremum of the exponents $\nu$ for which infinitely many reduced fractions $p/q$, with $q\ge2$, satisfy

$$
0<|z-p/q|<q^{-\nu}.
$$

Dirichlet's theorem gives infinitely many such fractions at $\nu=2$ for every irrational $z$. The difficult direction is ruling out infinitely many successes at any fixed $\nu>2$.

For our $y$, the paper proves the following stronger, explicit form of that exclusion: for every $\varepsilon>0$, there is a threshold $Q$ such that

$$
q\ge Q\quad\Longrightarrow\quad
|y-p/q|\ge q^{-(2+\varepsilon)}
\quad\text{for all integers }p,q.
$$

The threshold depends on $\varepsilon$. If you ask for $\varepsilon=0.001$ instead of $0.01$, you may need a different threshold. The result doesn't promise a single positive $c$ with error always at least $c/q^2$, and it doesn't prohibit isolated, spectacular approximations.

Our table can't test this conclusion. Even a long table says nothing by itself about what happens beyond every denominator threshold.

## Why divide by $\sqrt2$?

Let's keep the normalization visible. Set

$$
\theta=\arctan\sqrt2,\qquad x=2y=\frac{2\theta}{\sqrt2},
\qquad \beta=i\sqrt2.
$$

The double-angle identities then give

$$
e^{\beta x}=e^{2i\theta}
=\frac{1-2+2i\sqrt2}{1+2}
=\frac{-1+2\beta}{3}=\alpha.
$$

This exact identity connects a real number we're approximating to a complex number with simple algebraic coordinates. The powers $\alpha^j$ stay in $\mathbb Q(i\sqrt2)$, the numbers of the form $a+bi\sqrt2$ with rational $a,b$.

They also never repeat. Here's a short way to see that if you've met algebraic integers (roots of monic polynomials with integer coefficients). If $\alpha$ were a root of unity, both $\alpha$ and its conjugate would be algebraic integers, so their sum $-2/3$ would be one too. A rational algebraic integer must be an integer. That rules out $-2/3$. An equality between two distinct powers would make $\alpha$ a root of unity, so all the powers are distinct.

At the end we pass from $x$ to $y$ by dividing by 2. That's rational scaling, whose effect we can control. There's no corresponding general rule that lets us multiply or divide by $\sqrt2$ while keeping the exponent: an algebraic irrational multiplier needn't even preserve irrationality. For example, $\sqrt2\cdot\sqrt2=2$. The theorem here is about the displayed normalized number, and gives no exponent for the unscaled $\theta$.

## What can we do with those exact complex coordinates?

We can clear denominators into

$$
\mathbb Z[\beta]=\{a+b\beta:a,b\in\mathbb Z\}.
$$

This set is closed under addition and multiplication, since $\beta^2=-2$. More usefully,

$$
|a+b\beta|^2=a^2+2b^2.
$$

A nonzero element therefore has magnitude at least 1. If a determinant has entries in this set, its determinant does too, so the same lower bound applies whenever the determinant is nonzero.

Suppose now that $x$ admits approximations better than $q^{-\nu}$ for a fixed $\nu>2$, with arbitrarily large denominators. We select finitely many of them, $r_k=p_k/q_k$, and build interpolation centers

$$
(\alpha^j,\beta jr_1,\ldots,\beta jr_m).
$$

These are close to the points

$$
(e^{\beta jx},\beta jx,\ldots,\beta jx)
$$

on the complex curve $z\mapsto(e^z,z,\ldots,z)$. Their differences in the additive coordinates are $\beta j(r_k-x)$, which are small because the fractions are assumed to be too good.

The matrix records coefficients of polynomials expanded near the interpolation centers. Weighted degree bounds limit which monomials we use and which derivatives we prescribe. An inherited interpolation theorem proves that the prescribed conditions are independent enough to choose a square nonzero minor.

That's a substantial theorem. Counting monomials and counting conditions would only tell us independence is possible; it wouldn't prove independence. The actual proof uses algebraic geometry, including a vanishing theorem that supplies interpolation at sufficiently large heights. We'll use its conclusion here rather than try to reconstruct that geometry from undergraduate linear algebra.

## How does a small approximation error make a determinant too small?

Taylor expansion compares our approximate centers with the exact curve. It gives a sum of determinant terms. When two rows use the same transverse coefficient and the same Taylor order, that term vanishes because those rows are proportional. For a surviving term, we must either use sufficiently many high Taylor orders or sufficiently many factors of the small approximation errors.

Both possibilities give analytic savings. Once the parameters are chosen, these savings beat the arithmetic lower bound obtained by clearing denominators. The bounds concern the same nonzero minor, so they can't both hold. Our supposed unbounded supply of overaccurate fractions was impossible.

I find the denominator step particularly easy to underestimate. For example,

$$
(p/q+u)^3=(p/q)^3+3(p/q)^2u+3(p/q)u^2+u^3.
$$

The coefficient of $u^2$ needs only one factor of $q$ to become integral. Multiplying it by $q^3$ would also work, but we'd pay two unnecessary factors when deriving the lower bound for the original determinant. The construction keeps the savings from the derivative rows.

The powers of $\alpha$ in the matrix must stay as well. Having magnitude 1 doesn't make them arithmetically free: their denominator comes from powers of 3. Here there is another small analytic cost because $|\beta|=\sqrt2$, rather than 1. The proof includes that cost explicitly in its parameter estimates. Close to exponent 2, a fixed factor is manageable, but only after we've allowed room for it.

## How do we get from twice the number to the final answer?

Suppose we want an eventual bound at exponent $\nu>2$ for $y=x/2$. Choose $\lambda$ strictly between 2 and $\nu$. The bound for $x$ at exponent $\lambda$ gives

$$
|y-p/q|=\frac12|x-2p/q|\ge\frac12q^{-\lambda}
\ge q^{-\nu}
$$

once $q^{\nu-\lambda}\ge2$. That's why a rational factor of 2 is harmless here. We've paid for it using the small gap between the exponents.

The bound holds for unreduced fractions too. If $y$ were rational, its exact value could be written with arbitrarily large denominators and zero error. So the bound first proves irrationality. Dirichlet's theorem then gives $\mu(y)\ge2$, while the exclusion of every $\nu>2$ gives $\mu(y)\le2$.

## How does this fit with the earlier papers?

OpenAI's [paper on $\pi$](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026) supplies the weighted interpolation and determinant method. Casper's [rational-logarithm extension](../../The-irrationality-exponent-of-positive-rational-logarithms-is-2-October-7-2026/README.md) uses exact rational exponential coordinates, and his [rational-arctangent extension](../../The-irrationality-exponent-of-nonzero-rational-arctangents-is-2-October-7-2026/README.md) uses rational complex coordinates, clearing into the Gaussian integers $\mathbb Z[i]$.

Here the arithmetic changes to $\mathbb Z[i\sqrt2]$. The general statement covers nonzero real $x$ for which $e^{i\sqrt2x}$ lies in $\mathbb Q(i\sqrt2)$ and has distinct powers. The paper verifies those conditions for $x=2y$. It doesn't claim the same construction for every imaginary quadratic field or for points whose powers repeat.

*Casper initiated and directed the investigation. OpenAI coding agents contributed substantially to the mathematical adaptation, formal proof, verification work, and exposition. The inherited OpenAI framework and Mathlib are credited in the paper. See the [verification record](../lean/VERIFICATION.md) for formal-checking details; no external human peer review or exhaustive priority claim is asserted.*
