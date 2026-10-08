# A logarithm, two conjugates, and unusually good fractions

The exact number in this paper is

$$
x=\frac{\log(3+2\sqrt2)}{\sqrt2}\approx1.24645048028046102679,
$$

with the natural logarithm and 20 rounded decimal places. Here are some rational approximations:

| Fraction | Decimal value (rounded) | Absolute error (approximately) |
|---|---:|---:|
| $5/4$ | 1.250000000000 | 0.003549519720 |
| $86/69$ | 1.246376811594 | 0.000073668686 |
| $263/211$ | 1.246445497630 | 0.000004982650 |
| $1229/986$ | 1.246450304260 | 0.000000176021 |

These are good fractions, but we're interested in what an infinite sequence can achieve. Ryan Matthew Casper's [paper](../paper.pdf), dated 7 October 2026, proves $\mu(x)=2$, where $\mu$ is the irrationality exponent. You can follow the main mechanism with calculus and linear algebra; the interpolation theorem used inside it needs considerably more machinery.

## What exponent 2 tells us

For an irrational real number, $\mu(x)$ is the supremum of exponents $\nu$ for which infinitely many reduced fractions satisfy

$$
0<|x-p/q|<q^{-\nu},\qquad q>0.
$$

Dirichlet's approximation theorem gives $\mu(x)\ge2$. The paper proves the opposite inequality through this stronger statement: for each $\varepsilon>0$, some $Q$ satisfies

$$
q\ge Q\quad\Longrightarrow\quad |x-p/q|\ge q^{-2-\varepsilon}
$$

for every integer $p$ and positive integer $q$. This even covers unreduced fractions. It proves irrationality too, because a rational $x$ would have exact unreduced representations with unbounded denominators.

The threshold depends on $\varepsilon$. There's no permission to set $\varepsilon=0$, and we don't obtain a fixed $c>0$ such that every error is at least $c/q^2$. That stronger property is called bad approximability.

I find the distinction easier to see in our table. The fractions give individual successes; the theorem limits the rate at which successes can continue indefinitely. It doesn't forbid a spectacular approximation at some isolated denominator.

## Why divide the logarithm by $\sqrt2$?

Write $\beta=\sqrt2$ and $u=3+2\beta$. Then

$$
e^{\beta x}=u,\qquad e^{-\beta x}=u^{-1}=3-2\beta.
$$

Changing $\beta$ to $-\beta$ swaps these identities while keeping the same real $x$. Consequently, one fraction $r=p/q$ close to $x$ gives useful approximations to both $\beta x$ and $-\beta x$:

$$
|\beta r-\beta x|=|{-\beta r}-({-\beta x})|=\sqrt2\,|r-x|.
$$

That's why this normalization fits. We prove the approximation result for $x$ directly. Irrational scaling is not an invariance of the irrationality exponent, so the theorem doesn't automatically transfer to $\log u$.

You can also recognize the number from calculus:

$$
x=\int_0^1\frac{dt}{1-t^2/2}
=\sum_{n=0}^{\infty}\frac1{2^n(2n+1)}.
$$

The series is useful for computing digits. Obtaining the sharp irrationality exponent takes more than estimating this particular series remainder.

## The arithmetic works in pairs

We use the ring $\mathbb Z[\sqrt2]$, consisting of numbers $a+b\sqrt2$ with integer $a,b$. Conjugation sends one of these to $a-b\sqrt2$, and their product is

$$
N(a+b\sqrt2)=a^2-2b^2.
$$

For a nonzero ring element, this norm is a nonzero integer. Thus

$$
1\le|a+b\sqrt2|\,|a-b\sqrt2|.
$$

Neither factor has a positive universal lower bound. Powers of $3-2\sqrt2$ get arbitrarily small while their conjugates get large. Any argument that quietly replaces the product bound with a bound on one factor has lost the main difficulty.

## Build one determinant, estimate it twice

Assume overly good rational approximations exist at arbitrarily large denominators for one fixed $\nu>2$. Select finitely many such fractions. A weighted interpolation construction uses them, powers of $u$, and truncated Taylor series for $\log(1+t)$ to form a matrix.

Interpolation shows that the matrix has full row rank. We can therefore choose a square submatrix with nonzero determinant $\Delta_+$. Now keep those exact columns and change every arithmetic occurrence of $\sqrt2$ to $-\sqrt2$, obtaining $\Delta_-$. The column choice is fixed; choosing a different nonzero minor at the second sign wouldn't establish the relation we need.

Careful denominator clearing produces a single matrix over $\mathbb Z[\sqrt2]$. If its determinant is $z$, then

$$
z=C\Delta_+,\qquad \overline z=C\Delta_-,\qquad C>0.
$$

Here the bar denotes the quadratic conjugate, not complex conjugation. The norm inequality gives

$$
1\le C^2|\Delta_+\Delta_-|.
$$

On the analytic side, the good fractions make the additive coordinates close to the exponential curve at both signs. Taylor expansions then bound both determinants. Repeated low-order Taylor patterns create dependent rows, so the corresponding determinant terms vanish; higher-order terms and approximation errors provide the remaining smallness.

Clearing denominators can be expensive. We need the analytic product bound to overcome $C^2$, not just make each original determinant look small. The weighted construction retains useful denominator savings from the rows. Averaging the two logarithmic analytic estimates matches the doubled arithmetic cost, letting the argument reach every $\nu>2$.

That's the part worth carrying away: the two estimates apply to the conjugates of *one* arithmetic object. Otherwise the integer lower bound has nothing to attach to.

## Background and where to read next

The interpolation and Taylor-determinant framework comes from OpenAI's [work on $\pi$](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026), with substantial inherited ingredients from Casper's [rational-logarithm](../../The-irrationality-exponent-of-positive-rational-logarithms-is-2-October-7-2026/README.md) and [imaginary-quadratic](../../The-irrationality-exponent-of-arctan-sqrt2-over-sqrt2-is-2-October-7-2026/README.md) adaptations. The real quadratic case requires the paired estimate described here.

[Bashmakova and Zolotukhina's 2017 paper](https://www.mathnet.ru/eng/cheb531) studies a normalized logarithm family whose $d=2$ member equals $2x$. The present manuscript does not identify the strongest previous bound for this member or claim an exhaustive novelty search.

For the actual estimates, continue with the [master's version](ELIMS.md) or the [manuscript](../build/manuscript.md). The proved endpoint is this particular $x$; the generic theorem has explicit hypotheses in $\mathbb Q(\sqrt2)$, not arbitrary real quadratic fields.

*Casper initiated and directed the investigation. OpenAI coding agents contributed substantially to the mathematical adaptation, formal proof, verification work, and exposition. The paper credits OpenAI's inherited framework and Mathlib. Formal-checking details are in the [verification record](../lean/VERIFICATION.md); these checks are not external human peer review.*
