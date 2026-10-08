# Can fractions keep getting unusually close to log 2?

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

Look at $9/13$: it misses by less than one thousandth, despite having a denominator of only 13. That's pretty good. The fractions in the table get closer, but their denominators get bigger too. Can we keep finding fractions that do unusually well without needing enormous denominators?

The displayed decimals are rounded; none of these fractions equals the irrational value exactly.

Ryan Matthew Casper's [*The irrationality exponent of positive rational logarithms is 2*](../paper.pdf) answers the question about fractions. We'll start with what its title is saying, then look at the idea behind the proof. The [full manuscript](../build/main.tex) is available if you'd like to follow it further.

## What counts as unusually close?

You can always get a more accurate decimal approximation by keeping more digits. But writing those digits as a fraction gives a larger denominator, too. We'd like to give the fraction some credit for doing well with a small denominator.

One way to do that is to compare its error with one divided by the denominator squared. If the fraction is $p/q$, the target is $1/q^2$. For our example,

$$
1/13^2\approx0.00591716.
$$

The error of $9/13$ is smaller, so it beats that target. If we make the target harder by using $1/13^3\approx0.00045517$, it misses.

A theorem called Dirichlet's approximation theorem tells us that every irrational number has infinitely many fractions beating the square-denominator target. That includes lots of different denominators, however far out we go. We're counting distinct fractions in lowest terms, so writing $9/13$ as $18/26$ doesn't get us another one.

Now try a target between the square and the cube, say $1/q^{2.1}$. The paper proves that for $\log2$, this harder target eventually can't be beaten. After some denominator, *every* fraction has an error at least that large.

You might try 2.01 instead. Or 2.000001. The same conclusion holds for any fixed exponent greater than 2, although the point beyond which it holds can change. We aren't given a calculator-ready value for that point.

This is the meaning of “irrationality exponent 2”: infinitely many fractions beat the square target, while every fixed higher-power target can be beaten only finitely often.

Notice we haven't said that every fraction has error at least $1/q^2$. It would actually conflict with the Dirichlet result we just used. The paper also doesn't give a fixed positive constant $c$ making $c/q^2$ a lower bound for all fractions. There can still be some remarkably good approximations; the theorem restricts how often they can meet those harder targets.

## Why knowing it's irrational isn't enough

“Irrational” means no fraction hits the number exactly. It doesn't tell us how close the fractions get. Zero error and very small error are different questions, even if a calculator displays the same digits for both numbers.

The paper covers more than $\log2$. You can put any positive fraction or positive integer inside the natural logarithm, except 1. For instance, $\log3$, $\log(3/2)$, and $\log(1/2)$ all have exponent 2. The last one is negative, which is fine. We exclude 1 because $\log1=0$. A ratio like $\log2/\log3$ isn't one of the numbers this theorem addresses.

The proof also establishes irrationality. If one of these logarithms equaled $u/v$, we could rewrite it as $2u/(2v)$, $3u/(3v)$, and keep going. Those exact matches would have zero error even at enormous denominators. The paper's eventual positive lower bound applies to unreduced fractions too, so it rules that out.

## How could you prove something about every denominator?

Checking fractions one by one won't get us there. There's always another denominator waiting after the last one we checked. Instead, the proof assumes that exceptionally good fractions keep appearing, and works out a consequence that can't happen.

It uses those hypothetical fractions to construct a number with two incompatible properties: it must be at least a certain size, and it must be smaller than that size. The number is a *determinant*, calculated from a square table of numbers. You may already have seen the two-by-two rule:

$$
\det\begin{pmatrix}a&b\\c&d\end{pmatrix}=ad-bc.
$$

For a small example, take

$$
\det\begin{pmatrix}1&1\\1&1+1/1000\end{pmatrix}=1/1000.
$$

If we removed the $1/1000$, the rows would be identical and the determinant would be zero. Determinants of larger tables also vanish when two rows are identical. That gives the proof a way to use the relationships between its many entries.

The lower-bound idea is simple. A nonzero fraction whose denominator divides 1000 cannot have absolute value below $1/1000$. Multiplying it by 1000 gives a nonzero integer, and the smallest possible absolute value of a nonzero integer is 1. The paper does this with a much larger denominator, carefully keeping track of where all its factors come from.

For the upper bound, the proof uses the fact that the hypothetical fractions are very close to an exact exponential pattern. It expands functions in power series. Some terms carry powers of tiny approximation errors; others disappear because of repeated rows. The terms that remain can be bounded too, and the final estimate makes the determinant smaller than the lower bound allows.

There's an important difficulty tucked into that description: the determinant has to be nonzero. If it were zero, there'd be no conflict at all. Proving that is a substantial part of the paper. It involves constructing polynomials with prescribed local coefficients, much as you might choose a line to pass through two points, but with far more conditions and several variables. The full proof uses advanced geometry. The two-by-two example helps explain why a determinant is useful; it doesn't make that harder step disappear.

## Why an earlier paper about π helped

OpenAI's September 24, 2026 paper [*The irrationality exponent of π is 2*](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026) developed the framework this proof builds on. Its exponential pattern comes from complex numbers: $e^{2\pi i j}=1$ for every integer $j$, where $i^2=-1$. So all those inputs return the same value.

For logarithms, we have a pattern you can check with ordinary exponent rules:

$$
e^{\log2}=2,\qquad e^{2\log2}=4,\qquad e^{3\log2}=8.
$$

More generally, $e^{j\log a}=a^j$. If $a$ is rational, so are those powers. This lets the logarithm proof build a rational determinant near an exact exponential pattern, borrowing much of the earlier method.

But the values now change instead of all being 1. The new paper proves that the polynomial construction still works at these different points, and adjusts the estimates for fractions inside the logarithm and for the size of the logarithm itself. Those changes are where the extension does its work.

If you find a fraction closer to $\log2$ than $9/13$, it won't upset the theorem. You can ask which denominator powers its error beats, and then look for another. For any fixed power above 2, the theorem says the successes eventually stop. It doesn't tell you which fraction will be the last one.

*About the work: Ryan Matthew Casper initiated and directed the extension. OpenAI coding agents contributed substantially to the argument, formal proof and automated reviews, and assisted with these explanations. The [formal-proof notes](../lean/VERIFICATION.md) are there if you're curious; external human peer review has not been claimed.*
