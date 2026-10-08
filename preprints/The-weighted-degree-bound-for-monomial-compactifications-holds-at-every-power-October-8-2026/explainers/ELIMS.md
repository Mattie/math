# Degree bounds at every bundle power

For context, here's the natural logarithm of 2, rounded to 20 decimal places:

$$
\log2\approx0.69314718055994530942.
$$

Some familiar rational approximations are

| Fraction | Decimal value, rounded |
|---|---:|
| $9/13$ | 0.692307692308 |
| $61/88$ | 0.693181818182 |
| $445/642$ | 0.693146417445 |

The earlier [rational-logarithm paper](../../The-irrationality-exponent-of-positive-rational-logarithms-is-2-October-7-2026/README.md)
studies the possible rate of improvement in such approximations. Its proof
depends on interpolation: construct polynomials with prescribed local data,
control their degree, and use them in a determinant argument.

Ryan Matthew Casper's [*The weighted degree bound for monomial compactifications holds at every power*](../paper.pdf) strengthens the degree-control step. It turns
an eventual bound into a bound at every bundle power. The main proof is short
once the older geometric theorem is available, and it's worth seeing exactly
where that older theorem enters.

## A geometric family with polynomial coordinates

Choose finitely many monomials $x^{\alpha_j}$ in $d$ variables, including the
constant 1 and each variable $x_i$. Use them to map affine space into projective
space:

$$
x\longmapsto[x^{\alpha_j}]_j.
$$

Take the scheme-theoretic projective closure $X$. Roughly, this retains the
algebraic equations defining the construction, rather than merely closing up a
set of points. That distinction lets the statement work over finite fields too.

The hyperplane line bundle $L$ on $X$ comes with a constant-coordinate section
$s_0$. Where that coordinate is nonzero, we recover the original affine space.
In that region, dividing a global section $s$ of $L^n$ by $s_0^n$ gives a
polynomial $f$.

You can think of $s_0$ as the local reference used to write sections as functions.
“Global” requires the section to make sense across all of $X$. That's a real
restriction on $f$.

Assign nonnegative real weights $w_i$ to the variables and suppose every chosen
embedding monomial has weight at most $R$. The goal is

$$
\deg_w f\le nR\qquad\text{for every }n\ge0.
$$

Weighted degree takes the maximum of $\sum_i w_i\alpha_i$ over the nonzero terms.
With weights $(1,2)$, for example, $1+x^3y^2+y^3$ has weighted degree 7.

## The inherited theorem gets us started

The existing geometric result supplies some threshold $N$ such that the desired
bound holds for all $n\ge N$. It's a theorem for this actual compactification;
we aren't assuming eventual degree control for an arbitrary line bundle.

Suppose $n>0$. Raise a section $s$ to a positive integer power $k$ with $nk\ge N$.
The result is a section of $L^{nk}$ whose local coefficient is $f^k$. Now use the
eventual bound:

$$
\deg_w(f^k)\le nkR.
$$

Over a field, weighted degree is additive under multiplication of nonzero
polynomials. Order the terms first by their weights, then lexicographically to
break ties. The largest terms multiply to the largest product term, with a
nonzero coefficient. Consequently,

$$
k\deg_w f\le nkR,
$$

and division by $k$ settles the original power $n$.

This is the pleasant part: we don't have to calculate $N$. We can use its
existence to move a hypothetical small-power violation far enough up the family
to contradict the established theorem.

## Zero can't be multiplied into a large positive number

The argument above needs $n>0$. At $n=0$, a section is a global regular function,
and its powers still sit at bundle power zero.

Here the actual section $s_0$ matters. For every positive $k$, the product
$s^k s_0$ is a section of $L$, with local coefficient $f^k$. The positive-power
bound we've just proved therefore gives

$$
k\deg_w f\le R\qquad\text{for every }k\ge1.
$$

If $\deg_w f$ were positive, sufficiently large $k$ would violate this inequality.
So every term of $f$ has weight zero. We state the result as a support bound,
which also covers $f=0$ without assigning it a special degree.

The theorem works in any frame of $L$ on the fixed affine chart. Two such frames
differ by an invertible polynomial. Over a field those units are nonzero
constants, so changing the frame doesn't change which monomials occur. Changing
the affine coordinates themselves is a different operation.

## What a later proof can use

OpenAI's [$\pi$ manuscript](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026)
developed the weighted interpolation and determinant machinery. Casper's
rational-logarithm, rational-arctangent, and two normalized quadratic-period
papers adapted that machinery and share the compactification covered here.
The note also supplies the corresponding specialization for the original
$\pi$ construction.

Those arguments still need eventual surjectivity of a jet-restriction map to
produce sections with prescribed values and derivatives. This degree lemma
doesn't make that map surjective at every power. It doesn't compute an effective
irrationality constant or change any of the earlier endpoint theorems.

The earlier proofs can remain intact. When a new construction already supplies
a global section at a small power, we can now apply the degree estimate directly.
The [full note](../build/manuscript.md) gives the hypotheses to check before doing so.

*Casper initiated and directed this investigation. OpenAI coding agents
contributed substantially to the argument and assisted with this explanation.
The work credits OpenAI's released framework and Mathlib, and distinguishes
automated checking and model review from independent human review.*
