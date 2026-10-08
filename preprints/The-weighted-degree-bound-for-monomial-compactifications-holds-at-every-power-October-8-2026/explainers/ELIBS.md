# Weighted polynomial degree and powers

The natural logarithm of 2, rounded to 20 decimal places, is

$$
\log2\approx0.69314718055994530942.
$$

Here are a few nearby fractions:

| Fraction | Decimal value, rounded |
|---|---:|
| $9/13$ | 0.692307692308 |
| $61/88$ | 0.693181818182 |
| $445/642$ | 0.693146417445 |

Casper's [rational-logarithm paper](../../The-irrationality-exponent-of-positive-rational-logarithms-is-2-October-7-2026/README.md)
proves an irrationality-exponent result for numbers like this. Its argument uses
polynomials whose degree must stay within a specified limit.

Ryan Matthew Casper's [*The weighted degree bound for monomial compactifications holds at every power*](../paper.pdf) revisits that limit. The earlier ingredient
established it only after a sufficiently large power. This note gets the same
limit at every power. The [manuscript](../build/manuscript.md) contains the exact
statement; we'll start with the algebra that makes it possible.

## Degree grows predictably

If $f$ and $g$ are nonzero polynomials in one variable over a field, then

$$
\deg(fg)=\deg f+\deg g.
$$

Their leading coefficients multiply to a nonzero coefficient, so the highest
term survives. Repeating the multiplication gives $\deg(f^k)=k\deg f$.

For several variables, give each variable a nonnegative weight. With weights
$w_x=1$ and $w_y=2$, the polynomial

$$
f(x,y)=1+x^3y^2+y^3
$$

has term weights $0$, $7$, and $6$, respectively. Its weighted degree is 7.

The product rule remains true for weighted degree. If several terms have the
same weight, choose a consistent lexicographic order to break the tie. The last
term in this combined order has a nonzero coefficient, and the last term of a
product comes from the last terms of its factors. That prevents cancellation
from lowering the maximum weight.

## Which polynomials does the theorem constrain?

We aren't imposing a degree limit on every polynomial. The polynomials here
come from *global sections* of a particular geometric construction.

A section is an object defined consistently across a space. On one chosen
region, we can represent it by an ordinary polynomial. Requiring it to extend
across the whole space restricts which polynomials can occur.

The space is constructed by using a finite collection of monomials as projective
coordinates. That collection includes 1 and every ordinary coordinate variable.
If each chosen monomial has weighted degree at most $R$, the theorem says that
a section at bundle power $n$ has a polynomial coefficient with

$$
\deg_w f\le nR.
$$

“Bundle power” records which member of the geometric family the section belongs
to. The multiplication rule is the part we need: taking a $k$-th power of a
section at power $n$ produces a section at power $nk$, represented locally by
$f^k$.

## Use the large-power theorem, then divide

The inherited result gives a threshold $N$: the degree bound holds whenever the
bundle power is at least $N$.

Fix any positive $n$ and any eligible nonzero polynomial $f$ at that power.
Choose a positive integer $k$ so that $nk\ge N$. Apply the inherited theorem to
the powered section:

$$
k\deg_w f=\deg_w(f^k)\le nkR.
$$

Divide by $k$. We get $\deg_w f\le nR$, including at the small power we started
with. We never needed to find the numerical value of $N$; its existence lets us
choose a large enough $k$.

The zero polynomial causes no trouble. The theorem is stated term by term, so
there's no nonzero term that could exceed the bound.

## Power zero has its own argument

At $n=0$, multiplying $n$ by $k$ won't reach a positive threshold. So that trick
alone leaves a gap.

The construction provides a global section $s_0$ at power 1 which looks like 1
on our chosen region. If a power-zero section has local polynomial $f$, multiply
its $k$-th power by $s_0$. We now have a power-1 section with coefficient $f^k$.
The positive-power result gives

$$
k\deg_w f\le R
$$

for every positive integer $k$. A positive weighted degree would eventually make
the left side exceed $R$. Thus the weighted degree is zero. If some weights are
zero, this doesn't force the polynomial itself to be constant.

## Why keep a separate note?

OpenAI's [$\pi$ paper](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026)
supplied the weighted interpolation and determinant framework. Casper's
logarithm, rational-arctangent, and two normalized quadratic-period papers use
related constructions. This note gives them a stronger shared degree lemma
without changing their existing proofs.

Producing sections with prescribed values and derivatives is a separate issue.
That interpolation step still has a large-power requirement. We also haven't
shown that every polynomial within the degree limit extends globally.

For a new argument, the useful distinction is straightforward: once a global
section exists, this degree bound is available at every bundle power. Establishing
that the required section exists remains your next job.

*Casper directed the investigation. OpenAI coding agents contributed substantially
to the argument and assisted with this explanation. The paper credits the
inherited framework; automated review is distinct from human mathematical review.*
