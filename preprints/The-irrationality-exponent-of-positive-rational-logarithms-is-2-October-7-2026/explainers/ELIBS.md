# How much accuracy does a denominator buy?

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

The denominator of $9/13$ is only 13, and its error is already below one thousandth. The larger fractions do better still. We could also get closer by writing down more decimal places, but then the denominator would grow too. How much accuracy does each denominator buy?

The displayed decimals are rounded; none of these fractions equals the irrational value exactly.

This is the question behind Ryan Matthew Casper's [*The irrationality exponent of positive rational logarithms is 2*](../paper.pdf). We'll work through what the answer means, then enough of the proof to see why logarithms, polynomials and determinants end up in the same argument. The [manuscript](../build/main.tex) has the details.

## Let's give the fractions something to beat

Write a fraction as $p/q$, with positive denominator $q$, and compare its error with $1/q^2$. For $9/13$,

$$
\underbrace{|\log2-9/13|}_{\approx\,0.00083949}
<\underbrace{1/13^2}_{\approx\,0.00591716}.
$$

It does comfortably better than that target. But $1/13^3\approx0.00045517$, so it doesn't beat the cube-denominator target. The larger the exponent, the smaller the permitted error (we're using denominators greater than 1).

Now ask whether a target can be beaten infinitely often by distinct fractions in lowest terms. Rewriting $9/13$ as $18/26$ doesn't count as another success.

A classical result called Dirichlet's theorem says every irrational number has infinitely many fractions beating $1/q^2$. So the square target is quite generous in that sense. To learn something specific about $\log2$, we need to ask whether it can keep beating a harder target.

The paper's answer is that every fixed exponent bigger than 2 eventually becomes too demanding. Choose $2.1$, for instance. There's a denominator threshold $Q$ beyond which

$$
\left|\log2-\frac pq\right|\ge\frac1{q^{2.1}}
$$

for every integer numerator $p$ and integer denominator $q\ge Q$. You can replace 2.1 with 2.001, or with any other number strictly bigger than 2. You may need a different threshold each time, and the proof doesn't calculate it for you.

That's what “irrationality exponent 2” means here: square-scale approximations keep occurring, while every fixed higher-power target has only finitely many successes. Formally the exponent is the supremum of the powers admitting infinitely many positive-error approximations.

It's tempting to erase the extra 0.001 and announce a lower bound at exactly $1/q^2$. We can't do that. The result doesn't even give a fixed positive constant $c$ for a bound $c/q^2$. It leaves room for some very good fractions at the square scale.

The theorem also applies to $\log3$, $\log(3/2)$, and every other natural logarithm of a positive rational number except 1. Even $\log(1/2)$ is included; its being negative causes no problem. The threshold can depend on which logarithm we choose. A quotient such as $\log2/\log3$ is a different number and isn't covered by this statement.

## Why “irrational” doesn't already answer this

Irrationality tells us a fraction never hits the number exactly. It doesn't tell us how close a miss can be. A number could be irrational and still admit infinitely many errors below $q^{-10}$; we'd need more information to rule that out.

In this proof the approximation bound actually comes first. If a permitted logarithm were exactly $u/v$, then $ku/(kv)$ would give zero error at arbitrarily large denominators, violating the positive lower bound. That proves irrationality, and Dirichlet's theorem then gives the other half of the exponent-two result.

The difficult work is establishing the eventual bound. A table of excellent approximations won't prove it, however long we make the table.

## A little linear algebra helps

Suppose, temporarily, that the bound fails: for some fixed exponent above 2, exceptionally good fractions keep appearing at arbitrarily large denominators. The proof selects several, with their denominators spaced very far apart, and builds a matrix of rational numbers from them.

The matrix comes from polynomial interpolation. You already know the smallest example. Given values $y_1,y_2$ at distinct inputs $x_1,x_2$, we can find a line $b_0+b_1x$ taking those values. The equations have coefficient matrix

$$
\begin{pmatrix}1&x_1\\1&x_2\end{pmatrix},
\qquad \det=x_2-x_1\ne0.
$$

That nonzero determinant lets us solve for the coefficients of the line. The paper needs a much larger version in several variables, prescribing local Taylor coefficients while keeping the polynomial degree under control. Prescribing those coefficients is much like prescribing values and derivatives in calculus.

There's a considerable complication here. Having more unknown coefficients than equations doesn't guarantee that we can prescribe all the data; the equations might be dependent. The proof has to establish independence at its particular points. It does so using estimates on algebraic curves and further algebraic geometry. We'll leave that work in the [interpolation section](../build/sections/interpolation.tex), but we do need its conclusion: the matrix contains a square submatrix with a nonzero determinant.

Call that determinant $\Delta$. Because its entries are rational, $\Delta$ is rational too. Clear the denominators, and a suitable integer multiple of $\Delta$ is a nonzero integer. Its absolute value must be at least 1. Undo the multiplication and you get a lower bound for $|\Delta|$.

This part is familiar arithmetic. Keeping the multiplier small enough is much harder.

For the other estimate, the proof uses Taylor expansions around the exact exponential graph. The hypothetical approximations are so good that some expansion terms contain high powers of extremely small errors. In the remaining terms, repeated rows cause cancellations; avoiding those repetitions forces higher Taylor orders, which can also be controlled. After the estimates are put together, the determinant has to be smaller than its arithmetic lower bound.

We can't have both. The proof chooses its parameters so that, if the excellent approximations kept appearing, this contradiction would occur for sufficiently large polynomial degrees. That rules out the assumed supply of approximations.

## The connection with π

The framework came from OpenAI's September 24, 2026 paper [*The irrationality exponent of π is 2*](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026). Its construction uses the complex exponential's repeating values, $e^{2\pi i j}=1$. Good approximations to π give points close to those exact periods.

For our logarithms, there's an equally useful identity:

$$
e^{j\log a}=a^j.
$$

If $a$ is rational, the right side is rational. Approximations to $\log a$ therefore let the new proof construct rational points near the exponential graph, which is just what the determinant argument needs.

The difference is that the coordinates $a^j$ are distinct, whereas the π construction keeps returning to 1. The logarithm paper proves the interpolation result for these new centers and accounts for the extra denominators when $a$ is a fraction. It also adjusts the analytic estimates for the size of $\log a$. Much of the earlier machinery is reused, but these changes need actual proofs.

If you go back to $9/13$, you can now ask a more useful question than how many decimals it gets right: which powers of 13 does its error beat? The theorem doesn't prevent another fraction from doing much better. It says that, once you fix any target $q^{-2-\varepsilon}$ with $\varepsilon>0$, only finitely many fractions will beat it.

*About the work: Ryan Matthew Casper initiated and directed the extension. OpenAI coding agents contributed substantially to the argument, formalization and automated reviews, and assisted with these explanations. For the optional formal-proof background, see the [verification notes](../lean/VERIFICATION.md). External human peer review has not been claimed.*
