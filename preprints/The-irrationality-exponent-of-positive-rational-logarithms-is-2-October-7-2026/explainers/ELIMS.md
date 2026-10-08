# What makes 2 the cutoff for rational logarithms?

Here's the number we'll use: the natural logarithm of 2, rounded to 20 decimal places. It's the number whose exponential is 2.

$$
\log 2 \approx 0.69314718055994530942.
$$

A few fractions get close to it:

| Fraction | Decimal value (rounded) | Error (approximately) |
|---|---:|---:|
| $7/10$ | 0.700000000000 | 0.006852819440 |
| $9/13$ | 0.692307692308 | 0.000839488252 |
| $61/88$ | 0.693181818182 | 0.000034637622 |
| $445/642$ | 0.693146417445 | 0.000000763114 |

Going from $7/10$ to $9/13$ cuts the error quite a bit for a small increase in denominator. By $445/642$, we're within a millionth. How often can fractions do unusually well for the size of their denominators? That's the question we'll pursue.

The displayed decimals are rounded; none of these fractions equals the irrational value exactly.

Ryan Matthew Casper's [*The irrationality exponent of positive rational logarithms is 2*](../paper.pdf) answers the infinite version of that question. This is a companion explanation; the [manuscript](../build/main.tex) has the full argument.

## How often can we do that?

For an irrational number $x$, Dirichlet's theorem gives infinitely many reduced fractions satisfying

$$
0<|x-p/q|<q^{-2}.
$$

You can get to this result through the pigeonhole principle, by comparing fractional parts of multiples of $x$. So if we're trying to prove that a number is difficult to approximate, we can't hope to rule out the square-denominator scale. Every irrational number gets that much.

What we can ask is whether some larger exponent also works infinitely often. This leads to the *irrationality exponent*: the supremum of the exponents $\nu$ for which $0<|x-p/q|<q^{-\nu}$ holds for infinitely many distinct reduced fractions. Larger exponents allow smaller errors. We're asking for better approximations as we increase $\nu$, which is worth keeping straight when reading the inequalities.

The paper proves that, for every positive rational $a\ne1$,

$$
\mu(\log a)=2.
$$

Here and throughout, $\log$ is the natural logarithm. The concrete upper-bound statement is this: given any $\varepsilon>0$, there is an integer threshold $Q\ge2$ such that

$$
\left|\log a-\frac pq\right|\ge q^{-2-\varepsilon}
\qquad(p,q\in\mathbb Z,\ q\ge Q).
$$

Choose $\varepsilon=0.1$, or $0.001$, or something much smaller. Each choice works, although you may get a different threshold. The threshold also depends on $a$, and the proof doesn't calculate it explicitly. You can't put $\varepsilon=0$ into this statement, nor does it give a fixed positive $c$ with error always at least $c/q^2$. The finer behavior right at the square scale is still a separate question.

This covers $\log2$, $\log3$, and $\log(3/2)$, among others. It also covers $\log(1/2)$, which is negative. The excluded input 1 would give zero. We're dealing with the logarithms individually here, so a ratio such as $\log2/\log3$ isn't included.

Knowing that a logarithm is irrational wouldn't be enough to get this result. Irrationality only excludes zero error. It doesn't tell us whether errors of size $q^{-10}$ keep turning up. In fact, the paper gets irrationality from its eventual bound: if $\log a=u/v$, the unreduced fractions $ku/(kv)$ would have zero error at arbitrarily large denominators. Once that's excluded, Dirichlet supplies the lower bound 2 for the exponent.

## A nonzero rational number can't be arbitrarily small for free

The useful arithmetic fact is wonderfully uncomplicated. If a nonzero rational number has denominator dividing a positive integer $D$, its absolute value is at least $1/D$. Multiply by $D$ and you've got a nonzero integer, which has absolute value at least one.

The proof builds a rational determinant to which this fact applies. Suppose, for a fixed $\nu>2$, there were arbitrarily large denominators with error at most $q^{-\nu}$. Choose finitely many such approximations $r_i=p_i/q_i$, with the denominators very widely separated. Set $\xi=\log a$, and consider the centers

$$
(a^j,jr_1,\ldots,jr_m),\qquad 0\le j<K.
$$

These are near the exact points $(e^z,z,\ldots,z)$ at $z=j\xi$. Everything in a center is rational, and $a^0,a^1,\ldots$ are distinct because $a>0$ and $a\ne1$.

Around each center, the proof expands polynomials in coordinates adapted to the exponential graph. A finite packet of local Taylor coefficients is called a *jet*. Think of prescribing a value and several derivatives, except that there are now several variables and we assign different weights to them to reflect the denominator sizes.

This gives a linear map from polynomial coefficients to prescribed jets. If the map is onto, its matrix has full row rank, so we can select a nonzero square minor $\Delta_H$. The subscript keeps track of the permitted weighted degree.

Unfortunately, having more polynomial coefficients than conditions doesn't prove that the conditions are independent. That is where a substantial part of the argument sits. The [interpolation proof](../build/sections/interpolation.tex) controls algebraic curves that might follow the specified logarithmic directions too closely, then turns those curve estimates into the required degree-bounded interpolation. It uses advanced algebraic geometry; we don't get this rank statement from a clever count alone.

Once we have $\Delta_H\ne0$, clearing denominators gives a lower bound. The bookkeeping includes the fractions $r_i$, coefficients of the truncated logarithm series, and powers of the denominator of $a$. We need to retain all of them. A lower bound that accidentally forgets one denominator won't survive the comparison.

## Making the same determinant too small

For the upper bound, expand the rows around the exact exponential graph. The determinant expansion has two possible sources of smallness.

Terms with large auxiliary indices carry high powers of the tiny approximation errors $r_i-\xi$. If there aren't enough of those, many rows must share small auxiliary indices. Rows in the same group test the same entire functions. Reusing a Taylor order gives repeated rows and a zero determinant, so a surviving term must use different Taylor orders; the estimates for those orders give the needed decay.

This is a useful bit of determinant logic: dependence is bad when we're trying to prove the original minor is nonzero, but repeated rows in its expansion help us bound it. Lots of terms disappear, and the ones left are expensive in either approximation errors or Taylor order.

The [analytic estimates](../build/sections/determinant.tex) control the whole expansion, including truncation errors and the number of terms. Parameters are chosen first, then the finite list of approximations and their weights; only after these are fixed does the degree grow through suitable integer heights. Eventually the analytic upper bound falls below the arithmetic lower bound. That's the contradiction.

## Where π enters

The starting point was OpenAI's September 24, 2026 paper [*The irrationality exponent of π is 2*](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026). It developed the weighted interpolation and determinant framework used here. In its construction, the exact complex points are $2\pi i j$, with exponential coordinate $e^{2\pi i j}=1$.

For logarithms, the corresponding identity is $e^{j\log a}=a^j$. We still have exact rational exponential coordinates, but now they're different at each center. The extension proves interpolation for that arrangement and handles the new costs from the denominator of $a$ and the size of $|\log a|$. The inherited framework does substantial work; the changed centers and estimates are what let it reach this family of logarithms.

So you can still look for a particularly good fraction for $\log2$, and exponent 2 doesn't tell you how spectacular an individual find might be. What it rules out is an endless sequence beating a fixed target such as $q^{-2.001}$. Even there, it doesn't tell you where the last exception is.

*About the work: Ryan Matthew Casper initiated and directed the extension. OpenAI coding agents contributed substantially to its argument, formalization and automated reviews, and assisted with these explanations. The [formal proof and verification notes](../lean/VERIFICATION.md) are available separately; external human peer review has not been claimed.*
