# Polynomial degree bounds explained

Here's a number from the earlier work, rounded to 20 decimal places:

$$
\log 2\approx0.69314718055994530942.
$$

A few fractions get close:

| Fraction | Decimal value, rounded |
|---|---:|
| $9/13$ | 0.692307692308 |
| $61/88$ | 0.693181818182 |
| $445/642$ | 0.693146417445 |

The [earlier logarithm paper](../../The-irrationality-exponent-of-positive-rational-logarithms-is-2-October-7-2026/README.md)
studies how good these approximations can keep getting as the denominators grow.
The decimals here just help us recognize the number; printing them isn't a proof.

This companion explains Ryan Matthew Casper's [*All-power weighted degree bounds
for monomial compactifications*](../paper.pdf). It settles one polynomial rule
used inside that earlier argument. You can follow the main trick with the
polynomials you already know.

## Start with the highest power

Take

$$
f(x)=x^4+2x+1.
$$

Its degree is 4. If you multiply five copies together, the highest term is
$x^{20}$. There's only one way to get that term: choose $x^4$ from every copy.
Everything else has a smaller exponent, so nothing can cancel it.

Thus $f^5$ has degree 20. In general, a nonzero polynomial of degree $d$ has a
$k$-th power of degree $kd$.

That familiar fact does most of the work in this note.

## Why taking a power helps

The full proof has a geometric construction that sorts its allowed polynomial
expressions into levels $n=0,1,2,\ldots$. These expressions have to come from
objects defined on the whole geometric space. An arbitrary polynomial doesn't
automatically qualify.

Two rules matter here. Multiplying expressions adds their levels. And the older
theorem puts a degree limit on expressions at sufficiently large levels.

For a concrete illustration, suppose the degree limit is $3n$ at level $n$, and
the older theorem starts working at level 5. Those numbers are an example; we
haven't calculated an actual starting level for the paper's construction.

Could our degree-4 polynomial qualify at level 1? The desired limit there is 3,
but the older theorem can't directly check that level.

Raise it to the fifth power. If $f$ qualified at level 1, then $f^5$ would qualify
at level 5. Now the older theorem applies, giving a maximum degree of
$3\times5=15$. We already know its degree is 20.

That's impossible. The original polynomial couldn't qualify at level 1.

The same reasoning works at any positive level. If a polynomial exceeds its
degree limit, taking powers multiplies the excess too. We can move the problem
to a level where the older theorem sees it.

## The paper gives different variables different weights

For a term with several variables, ordinary degree adds the exponents. For instance,
$x^3y^2$ has degree $3+2=5$.

The paper also allows a *weighted* degree. Give $x$ weight 1 and $y$ weight 2,
and that same term has weighted degree

$$
3\times1+2\times2=7.
$$

A polynomial's weighted degree is the largest weight of its nonzero terms.
Taking its $k$-th power still multiplies that degree by $k$. Proving this needs
a little more care because several terms can tie for the largest weight, but
the same power argument then goes through.

Level zero needs a separate step. The construction supplies a particular level-1
expression that looks like the constant 1 on the region where we're writing
polynomials. Multiply it by arbitrarily large powers of a level-zero expression.
The resulting expressions stay at level 1, so their degree has a fixed upper
limit. A positive degree couldn't keep growing that way. The original weighted
degree must be zero. (A variable with weight zero can still appear.)

## Where this fits in the earlier papers

OpenAI's [paper on the irrationality exponent of $\pi$](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026)
developed a method using polynomials, prescribed values and derivatives, and
determinants. Casper's later papers adapted that framework to logarithms,
arctangents, and two related quantities involving $\sqrt2$.

This note improves the shared degree rule: it works at every level, including
zero. Another part of the argument still needs sufficiently large levels to
produce the polynomials with the prescribed values and derivatives. We haven't
removed that requirement or proved a new result about approximating a number.

You can keep reading the earlier papers as they stand. If a future argument
needs their degree rule at a small level, this is the note to reach for.

*Casper directed the investigation. OpenAI coding agents contributed substantially
to the argument and assisted with this explanation. The paper credits OpenAI's
original framework and distinguishes automated review from human review.*
