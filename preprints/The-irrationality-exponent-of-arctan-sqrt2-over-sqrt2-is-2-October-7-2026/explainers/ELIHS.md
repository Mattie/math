# How well can fractions approximate this number?

Here's the number we're studying, with the arctangent in radians and the result rounded to 20 decimal places:

$$
y=\frac{\arctan\sqrt2}{\sqrt2}\approx0.67551085885603996302.
$$

We can get reasonably close with fractions:

| Fraction | Decimal value (rounded) | Absolute error (approximately) |
|---|---:|---:|
| $169/250$ | 0.676000000000 | 0.000489141144 |
| $25/37$ | 0.675675675676 | 0.000164816820 |
| $102/151$ | 0.675496688742 | 0.000014170114 |
| $331/490$ | 0.675510204082 | 0.000000654774 |

The first fraction is just our number rounded to three decimal places. The second does better with a denominator of only 37. That's a useful improvement: a longer decimal isn't always the most economical fraction.

All the displayed decimals are rounded. None of these fractions equals $y$ exactly, and printing more digits wouldn't prove that $y$ is irrational.

Ryan Matthew Casper's [paper](../paper.pdf), dated 7 October 2026, proves that this exact number has *irrationality exponent 2*. The [full manuscript](../build/manuscript.md) gives the proof. We'll work through what the result means and the main reason a proof is possible.

## What does the 2 measure?

Suppose a fraction $p/q$ is in lowest terms, with $q>0$. We compare its error with powers of its denominator. One useful target is

$$
0<|y-p/q|<\frac1{q^2}.
$$

For $331/490$, the error is about $0.000000655$, while $1/490^2$ is about $0.00000416$. So that fraction comfortably meets the target.

A theorem called Dirichlet's approximation theorem says that every irrational number has infinitely many fractions meeting this squared-denominator target. Getting some good fractions isn't unusual. The interesting question is how much better we can keep doing.

Try replacing 2 with 3. At denominator 1,000, the permitted error falls from one millionth to one billionth. Or replace 2 with just 2.01. The improvement is smaller, but it becomes increasingly demanding as the denominator grows.

The paper proves that, for any fixed positive $\varepsilon$, there is a denominator threshold beyond which every fraction obeys

$$
|y-p/q|\ge\frac1{q^{2+\varepsilon}}.
$$

You choose $\varepsilon$ first; the threshold may depend on it. There can still be exceptional fractions below the threshold. We can't set $\varepsilon=0$, and we haven't obtained one fixed positive constant $c$ making all errors at least $c/q^2$.

“Exponent 2” means that 2 is the supremum of the powers for which infinitely many reduced fractions have positive error smaller than $1/q$ raised to that power. Here Dirichlet supplies the infinitely many successes at 2, and the new proof rules them out at every fixed power above 2.

## Why this arctangent, divided by a square root?

There's a calculus description you may find more familiar:

$$
y=\int_0^1\frac{dt}{1+2t^2}.
$$

You can check it by differentiating $\arctan(\sqrt2t)/\sqrt2$. It gives us a definite integral with a simple rational function, although that alone doesn't tell us how well fractions approximate its value.

To get the arithmetic we need, set $\theta=\arctan\sqrt2$. The double-angle identities give

$$
\cos(2\theta)=-\frac13,\qquad
\sin(2\theta)=\frac{2\sqrt2}{3}.
$$

So a point on the unit circle, despite having a fairly inconvenient angle, has these exact coordinates. We package the point as

$$
\alpha=\frac{-1+2i\sqrt2}{3},\qquad i^2=-1.
$$

Multiplying complex numbers on the circle adds their angles. Repeated multiplication therefore gives exact points for $2\theta,4\theta,6\theta,\ldots$. Their coordinates stay in a controlled family involving integers, fractions, and $\sqrt2$.

Our proof is set up for $x=2\theta/\sqrt2=2y$: multiplying $x$ by $i\sqrt2$ gives $2i\theta$, the complex exponent corresponding to the angle $2\theta$. At the end we divide $x$ by the ordinary integer 2.

The division by $\sqrt2$ is part of the theorem's starting point. You can't first prove a result about $\theta$ and assume that irrational scaling preserves it. Multiplying by an irrational algebraic number can even turn an irrational number into a rational one: $\sqrt2\cdot\sqrt2=2$. This paper doesn't establish exponent 2 for the unscaled $\arctan\sqrt2$.

## How can arithmetic rule out endlessly good fractions?

I find it helpful to start with a very small arithmetic observation. A nonzero integer has absolute value at least 1. It can't be $0.000001$.

The proof needs a complex version. For integers $a,b$,

$$
|a+bi\sqrt2|^2=a^2+2b^2.
$$

If $a+bi\sqrt2$ isn't zero, the right side is a positive integer. Its magnitude is therefore at least 1 as well.

Now suppose we could approximate $x=2y$ too well with arbitrarily large denominators, at one fixed power above 2. The proof selects several such fractions and builds a matrix from them and from powers of $\alpha$. A determinant is a number calculated from a square matrix; for a two-by-two matrix its formula is $ad-bc$.

There are two jobs. First, show that a suitable determinant isn't zero. Second, use the extremely good approximations to make its magnitude very small. After carefully clearing denominators, the determinant has the form $a+bi\sqrt2$, so making it nonzero and smaller than 1 is impossible.

The second job uses Taylor expansions, which you'll recognize from calculus. The first uses a much deeper interpolation theorem: we prescribe values and derivatives of polynomials at many points and prove that enough independent choices are possible. A full proof needs algebraic geometry. We can understand the contradiction without pretending that a few calculus formulas establish that theorem.

The denominator calculations also have to be good enough. Clearing too many denominator factors gives a weaker estimate, which can spoil the contradiction near exponent 2. And the points $\alpha^j$ must never repeat; the manuscript proves that for our exact $\alpha$.

## Where did this method come from?

OpenAI's [work on the irrationality exponent of $\pi$](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026) supplied the interpolation and determinant framework. Casper's preceding papers adapted it to [logarithms of positive rational numbers other than 1](../../The-irrationality-exponent-of-positive-rational-logarithms-is-2-October-7-2026/README.md) and [arctangents of nonzero rational numbers](../../The-irrationality-exponent-of-nonzero-rational-arctangents-is-2-October-7-2026/README.md). Here $\sqrt2$ isn't rational, so another arithmetic adaptation is needed.

The proof ultimately gives the stated bound even for unreduced fractions. If $y$ were rational, we could rewrite that exact fraction with arbitrarily large denominators and zero error, contradicting the bound. So $y$ is irrational; Dirichlet then supplies exponent 2 from below.

You can still improve on $331/490$. The theorem says what an infinite sequence of such improvements cannot keep achieving.

*Casper initiated and directed the investigation. OpenAI coding agents contributed substantially to the mathematics, formal proof, verification work, and exposition. The paper credits OpenAI's inherited framework and Mathlib. The [verification record](../lean/VERIFICATION.md) gives the formal-checking details; external human peer review and an exhaustive priority claim are not asserted.*
