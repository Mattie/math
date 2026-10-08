# Weighted degree bounds for global sections

If your doctoral work is outside algebraic geometry, the notation in Ryan
Matthew Casper's [*The weighted degree bound for monomial compactifications holds at every power*](../paper.pdf) can conceal how little new geometry the main
argument needs. The substantial geometric input is inherited. The strengthening
comes from taking powers and keeping track of degree exactly.

The useful claim is this: for the specified monomial compactification, every
global section of the $n$-th hyperplane-bundle power has affine polynomial
coefficients of weighted degree at most $nR$, for every $n\ge0$. The inherited
result had supplied this estimate only for sufficiently large $n$.

## The objects behind the notation

Let $K$ be a field. Choose a finite indexed family
$(\alpha_j)_{j\in J}\subset\mathbb N^d$ containing $0,e_1,\ldots,e_d$; repeated
exponents are allowed. Define the graded algebra

$$
S=K[t x^{\alpha_j}:j\in J]\subset K[x_1,\ldots,x_d,t],
$$

where the grading is by the exponent of $t$, and put $X=\operatorname{Proj}S$.
This is the scheme-theoretic projective closure of the monomial map
$x\mapsto[x^{\alpha_j}]_j$. Defining it through $S$ avoids an ambiguity about
closures of rational points over finite fields.

The induced hyperplane bundle is $L$. A line bundle is locally a copy of the
structure sheaf, although its local copies may be glued with nontrivial
transition functions. A frame chooses such a local identification. A section
can then be written as a function times that frame.

Choose an index for the zero exponent. Its coordinate section $s_0$ is
invertible on the corresponding standard chart $U$. The coordinate monomials
ensure that $U\simeq\mathbb A_K^d$, with coordinate ring $K[x_1,\ldots,x_d]$.
Hence a global section $s\in H^0(X,L^n)$ has polynomial coefficient

$$
f=\left.s/s_0^n\right|_U.
$$

This coefficient need not have been given by a homogeneous polynomial of degree
$n$ in the embedding coordinates. Assuming that would introduce precisely the
sort of projective-normality issue the argument avoids.

Fix nonnegative real weights $w_i$ and an embedding budget $R$ with
$w\cdot\alpha_j\le R$ for all $j$. The theorem asserts

$$
w\cdot\alpha\le nR
\quad\text{whenever the coefficient of }x^\alpha\text{ in }f\text{ is nonzero}.
$$

The support formulation handles the zero polynomial directly. For $f\ne0$, it
is equivalent to $\deg_w f\le nR$.

## Exact multiplicativity is the algebraic hinge

For nonzero polynomials over a field,

$$
\deg_w(fg)=\deg_w f+\deg_w g.
$$

The inequality from above is immediate. Equality needs a term that survives.
Order exponents by weighted degree and break ties lexicographically. This total
order is compatible with addition, and each finite support has a largest
element. The largest exponent of $fg$ is the sum of the largest exponents of
$f$ and $g$; its coefficient is the product of their leading coefficients.
It cannot vanish over a field.

This works with arbitrary nonnegative real weights, including zero weights, and
in positive characteristic. The argument uses ordered supports rather than a
binomial coefficient that might vanish in characteristic $p$. In particular,
$\deg_w(f^k)=k\deg_w f$ for every positive $k$.

## Positive powers: move above the threshold

The inherited eventual coefficient theorem, specialized to this exact $X$ and
$L$, gives $N$ such that the bound holds for all bundle powers $m\ge N$.

Fix $n>0$ and $s\in H^0(X,L^n)$. Choose $k>0$ with $nk\ge N$. Tensoring the
section with itself gives
$s^{\otimes k}\in H^0(X,L^{nk})$, whose coefficient in the corresponding frame
is $f^k$. The eventual bound yields

$$
k\deg_w f=\deg_w(f^k)\le nkR.
$$

Dividing by $k$ proves the claim at the original $n$. Any positive-power
counterexample would generate arbitrarily high-power counterexamples, so the
eventual theorem already excludes it.

This deduction is conditional on the established eventual theorem. The concrete
formal result discharges that condition using the inherited monomial
compactification theorem; it doesn't quietly assume the desired small-power
bound.

## Power zero: use a section we actually have

At $n=0$, a section is a global regular function, and tensor powers cannot move
it out of degree zero. The positive-power argument therefore doesn't cover this
case by itself.

For each $k>0$, form $s^k s_0\in H^0(X,L)$. Its coefficient in the $s_0$ frame
is $f^k$. Applying the already established degree-1 result gives

$$
k\deg_w f\le R\qquad\text{for every }k>0.
$$

Thus $\deg_w f\le0$. Nonnegative weights then force every supported monomial to
have weight zero. This statement needn't make $f$ constant if a coordinate has
weight zero. The zero polynomial again satisfies the support bound vacuously.

The availability of $s_0$ is a concrete feature of the construction. We aren't
postulating a suitable positive-degree section for an arbitrary line bundle.

Finally, two frames of $L$ on $U$ differ by a unit in the polynomial ring over
$K$. Such a unit is a nonzero constant. Scalar multiplication preserves support,
so the estimate holds in every frame on this fixed chart. It is not a statement
about arbitrary changes of affine coordinates.

## The connection to irrationality-exponent proofs

OpenAI's [September 24, 2026 $\pi$ paper](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026)
provided a weighted interpolation and determinant framework. Casper's
[rational-logarithm](../../The-irrationality-exponent-of-positive-rational-logarithms-is-2-October-7-2026/README.md)
and subsequent arctangent and normalized quadratic-period preprints use related
geometry. Their shared construction supplies the monomial budget and the
constant and coordinate monomials required here.

In those arguments, global sections furnish degree-controlled polynomials that
realize prescribed weighted jets. Interpolation provides a nonzero determinant;
arithmetic and analytic estimates then constrain it. This note strengthens the
coefficient-degree estimate for any global section already in hand. It does not
establish jet-surjectivity at every power, calculate a vanishing threshold, or
imply that every polynomial satisfying the budget extends globally.

The underlying tensor-power principle is standard. The contribution is a
separate, reusable formal theorem tied to the actual constructions, including
the power-zero and frame details. The four earlier arguments remain valid as
written, with their eventual hypotheses.

## Formal scope

The main Lean declaration is `Degree.monomial_all_supportBound`.
`Degree.logarithm_all_supportBound` specializes it to the construction shared by
the four Casper preprints, while `Degree.admissible_all_supportBound` handles
the original $\pi$ library's admissible construction.

The [verification record](../VERIFY.md) identifies the five new modules, the
matched dependency sources, native checking, and the selected proof export
accepted by Nanoda and replayed by Lean 4.34.0. The independent automated reviewer
checked the specification and freshly compiled the modules; it audited the
recorded replay outcomes without rerunning those checkers. Formal checking and
model review don't establish novelty or substitute for independent human review.

For an application, first verify that your compactification includes the
constant and ordinary coordinates and satisfies the monomial weight budget.
Once those hypotheses hold, a global section at any natural power gets the
coefficient estimate. You can then treat the existence of the desired section
as a separate interpolation problem.

*Casper initiated and directed the investigation. OpenAI coding agents
contributed substantially to the argument, formalization, automated reviews,
and this explanation. The paper credits OpenAI's released manuscript and
library and Mathlib.*
