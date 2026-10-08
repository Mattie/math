# Why the real quadratic case needs both embeddings

Start with the number itself, using the natural logarithm:

$$
x=\frac{\log(3+2\sqrt2)}{\sqrt2}\approx1.24645048028046102679.
$$

That decimal is rounded to 20 places. Some useful approximations are:

| Fraction | Decimal value (rounded) | Absolute error (approximately) |
|---|---:|---:|
| $5/4$ | 1.250000000000 | 0.003549519720 |
| $86/69$ | 1.246376811594 | 0.000073668686 |
| $263/211$ | 1.246445497630 | 0.000004982650 |
| $1229/986$ | 1.246450304260 | 0.000000176021 |

Ryan Matthew Casper's [paper](../paper.pdf), dated 7 October 2026, proves that $\mu(x)=2$. Here $\mu(x)$ is the supremum of the exponents $\nu$ for which infinitely many reduced fractions have positive error below $q^{-\nu}$. We'll concentrate on the step that makes the real quadratic adaptation work. The [manuscript](../build/manuscript.md) supplies the detailed estimates.

## What has to be ruled out?

Fix $\nu>2$. The proof assumes that $|x-p/q|\le q^{-\nu}$ occurs at arbitrarily large positive denominators and derives a contradiction. It ultimately gives

$$
\exists Q\ge2\quad\forall p,q\in\mathbb Z,\quad
q\ge Q\Longrightarrow |x-p/q|\ge q^{-\nu}.
$$

There are no coprimality restrictions in this statement. Consequently $x$ must be irrational: an exact rational representation could otherwise be rescaled to unbounded denominators. Dirichlet gives the lower bound $\mu(x)\ge2$, and the eventual estimate excludes every exponent above 2.

The conclusion allows exceptional approximations below $Q$, and it doesn't provide an effective formula for $Q$. Nor does it assert bad approximability, the stronger uniform bound $|x-p/q|\ge c/q^2$ for some $c>0$.

## The small-conjugate problem

Put $\beta=\sqrt2$, $u=3+2\beta$, and $\mathcal O=\mathbb Z[\beta]$. There are two real embeddings

$$
\sigma_\pm(a+b\beta)=a\pm b\sqrt2.
$$

For nonzero $z\in\mathcal O$, its norm is a nonzero integer, so

$$
1\le|\sigma_+(z)|\,|\sigma_-(z)|.
$$

If you're used to imaginary quadratic arguments, it's tempting to read this as a useful lower bound on one determinant. It isn't. The powers of $u^{-1}=3-2\sqrt2$ tend to zero, even though their norms are all 1. We need to estimate the other embedding too.

Our normalization gives precisely the compatible identities

$$
e^{\beta x}=u,\qquad e^{-\beta x}=u^{-1}.
$$

Both power sequences have distinct terms. One rational approximation $r_k$ to $x$ therefore supplies small errors at both signs, with equal magnitudes $\beta|r_k-x|$. This is a direct argument about the normalized logarithm. Multiplication by $\sqrt2$ does not automatically preserve its irrationality exponent.

## One column choice throughout

Select finitely many very good approximants $r_k=p_k/q_k$ and give them weights $w_k=\lceil\log q_k\rceil$. At sign $\varepsilon\in\{+1,-1\}$, build a matrix from weighted monomials evaluated through the local coordinates

$$
Y=u^{\varepsilon j}(1+t),\qquad
X_k=\varepsilon\beta j r_k+G_k(t)+v_k,
$$

where $G_k$ is a rational truncation of $\log(1+t)$. Rows extract specified coefficients in $t,v_1,\ldots,v_m$; columns are monomials of bounded weighted degree. The auxiliary $v_k$ here are formal variables.

The inherited interpolation theorem makes the positive-sign matrix surjective onto its rows. Choose a nonzero square minor $\Delta_+$ containing every row. Define $\Delta_-$ using the **same columns** at the negative sign.

That's a rather specific requirement, and it's where a plausible sketch can go wrong. Separate existence proofs for two nonzero minors wouldn't tell us that their product is an arithmetic norm.

Instead, denominator clearing constructs one order-valued matrix $B$. Its entries are built from integers, $\beta$, powers of $u$, and cleared logarithm polynomials before either embedding is applied. A common positive factor $C$ then satisfies

$$
\sigma_\pm(\det B)=C\Delta_\pm.
$$

Since $\Delta_+\ne0$, the order determinant is nonzero, and hence

$$
1\le C^2|\Delta_+|\,|\Delta_-|.
$$

This also proves $\Delta_-\ne0$. We didn't need to select it again.

## Why the doubling doesn't spoil exponent 2

Let $M$ be the number of rows and $H$ the weighted degree bound. After taking logarithms, the arithmetic estimate has the form

$$
\frac{\log|\Delta_+|+\log|\Delta_-|}{2MH}
\ge -(1-b)-E_{\rm ar},
$$

where $b$ records the denominator savings contributed by the rows, and $E_{\rm ar}$ collects the additional costs. Keeping those row savings is necessary near exponent 2.

At each sign, compare the matrix coordinates with the same exponential curve, now near

$$
j(\varepsilon\beta x)+\log(1+t).
$$

The truncation $G_k(t)$ stays unchanged at the negative sign. Both signs have identical approximation-error sizes, and one sufficiently large analytic disc accommodates both sets of centers.

Taylor expansion gives two possible sources of determinant smallness. Many low-order terms force repeated Taylor patterns and determinant cancellation. Otherwise the transverse errors occur often enough to provide a strong approximation saving. Uniformly in the selected columns, each sign receives an estimate of the form

$$
\frac{\log|\Delta_\pm|}{MH}
\le E_{\rm an}+o(1)+\max\{-c_H,-\nu(A(1-\eta)-b)\}.
$$

The parameters are chosen so that either alternative contradicts the arithmetic lower bound. Taking the average of these two upper bounds preserves their strength. Both sides doubled together; there is no leftover factor of two weakening the desired exponent.

All the fractions and weights are fixed before $H$ tends to infinity. That order is useful to keep in view: an interpolation threshold depending on the chosen centers is harmless, but choosing new centers after using that threshold would be a different argument.

## How this fits the earlier papers

OpenAI's [paper on the irrationality exponent of $\pi$](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026) supplies the weighted interpolation and determinant framework. Casper's [rational-logarithm](../../The-irrationality-exponent-of-positive-rational-logarithms-is-2-October-7-2026/README.md) and [imaginary-quadratic](../../The-irrationality-exponent-of-arctan-sqrt2-over-sqrt2-is-2-October-7-2026/README.md) papers supply preceding adaptations. The present proof retains those substantial ingredients and adds the common real quadratic matrix with both analytic estimates.

[Bashmakova and Zolotukhina](https://www.mathnet.ru/eng/cheb531) studied $\sqrt d\log((\sqrt d+1)/(\sqrt d-1))$; its $d=2$ member is $2x$. [Polyanskii](https://arxiv.org/abs/1501.06752) studies related quadratic families. The historical comparison in the manuscript does not establish the strongest prior bound for this exact target.

The generic theorem stays within $\mathbb Q(\sqrt2)$ and requires explicit compatible exponential data. For extending the argument, those hypotheses and the uniform analytic estimates are the places to start checking; the endpoint alone doesn't establish a theorem for every real quadratic field.

*Casper initiated and directed the investigation. OpenAI coding agents contributed substantially to the mathematical adaptation, formal proof, verification work, and exposition. The paper credits OpenAI's inherited framework and Mathlib. The [verification record](../lean/VERIFICATION.md) describes the formal checks; these checks are not external human peer review.*
