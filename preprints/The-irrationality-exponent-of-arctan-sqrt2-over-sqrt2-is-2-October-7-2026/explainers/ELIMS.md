# Why does this normalized arctangent have exponent 2?

Our target, using radians and rounding to 20 decimal places, is

$$
y=\frac{\arctan\sqrt2}{\sqrt2}\approx0.67551085885603996302.
$$

These fractions give a first look at its rational approximations:

| Fraction | Decimal value (rounded) | Absolute error (approximately) |
|---|---:|---:|
| $169/250$ | 0.676000000000 | 0.000489141144 |
| $25/37$ | 0.675675675676 | 0.000164816820 |
| $102/151$ | 0.675496688742 | 0.000014170114 |
| $331/490$ | 0.675510204082 | 0.000000654774 |

The improvement from $169/250$ to $25/37$ is already enough to show why decimal rounding isn't the whole approximation problem. We want to compare the error with the denominator used to achieve it. All the decimals above are rounded, and none of the fractions equals the exact target.

Ryan Matthew Casper's [paper](../paper.pdf), dated 7 October 2026, proves that $y$ has irrationality exponent 2. The [manuscript](../build/manuscript.md) contains the complete argument. We'll concentrate on how complex arithmetic and interpolation combine to exclude exponents above 2, with a little more detail where the extension actually changes the proof.

## What exactly are we ruling out?

For irrational $z$, define $\mu(z)$ as the supremum of those $\nu$ for which

$$
0<|z-p/q|<q^{-\nu}
$$

has infinitely many distinct reduced rational solutions with $q\ge2$. Dirichlet gives $\mu(z)\ge2$. To prove equality, we need an upper bound at every fixed exponent above 2.

The result here has the useful quantified form

$$
\forall\nu>2\;\exists Q\ge2\;\forall p,q\in\mathbb Z:
\quad q\ge Q\Longrightarrow |y-p/q|\ge q^{-\nu}.
$$

Fractions in this bound needn't be reduced. The threshold is uniform in $p,q$, after $\nu$ is fixed. It can depend on $\nu$, so taking a limit $\nu\downarrow2$ doesn't give a uniform lower bound $c/q^2$. We also shouldn't expect a finite list of good approximations to settle an eventual statement.

## What is the useful exact identity?

Put $\beta=i\sqrt2$ and $x=2y$. The double-angle formula gives

$$
e^{\beta x}=e^{2i\arctan\sqrt2}
=\frac{-1+2\beta}{3}=\alpha.
$$

We have exchanged a troublesome real constant for a point with controlled arithmetic on the unit circle. Its powers lie in $\mathbb Q(\beta)$, and they are distinct. Indeed, a root of unity is an algebraic integer, as is its conjugate, but

$$
\alpha+\overline\alpha=-\frac23
$$

is a rational noninteger. It therefore cannot be the sum of two algebraic integers. Since $\alpha\ne0$, a repeated power would force a positive power to equal 1, which we've just ruled out.

The generic theorem handles a nonzero real $x$ whenever

$$
e^{\beta x}=U/D,\qquad U\in\mathbb Z[\beta],\quad
D\in\mathbb Z_{>0},
$$

and the powers of $U/D$ are distinct. “Non-torsion” is the usual name for that last condition. We don't assume the determinant estimate as part of the input; the proof constructs it from these arithmetic conditions.

The normalization deserves some care. We prove the statement for $x=2\arctan(\sqrt2)/\sqrt2$, then divide by the rational number 2. Multiplication by an algebraic irrational number has no general exponent-preservation rule. It can even destroy irrationality, as $\sqrt2\cdot\sqrt2=2$ shows. Thus this theorem makes no claim that the unscaled $\arctan\sqrt2$ has exponent 2.

## Where did the determinant method come from?

OpenAI's [work on $\mu(\pi)=2$](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026) supplies the weighted interpolation framework and much of the proof infrastructure. Casper's preceding [rational-logarithm paper](../../The-irrationality-exponent-of-positive-rational-logarithms-is-2-October-7-2026/README.md) uses $e^{j\log r}=r^j$ for positive rational $r\ne1$. His [rational-arctangent paper](../../The-irrationality-exponent-of-nonzero-rational-arctangents-is-2-October-7-2026/README.md) instead uses

$$
e^{2i\arctan r}=\frac{1-r^2+2ir}{1+r^2}\in\mathbb Q(i)
$$

for rational $r$. It clears determinants into $\mathbb Z[i]$ and handles the nonzero torsion exceptions using the $\pi$ theorem.

The present target requires $\mathbb Z[i\sqrt2]$. Its norm is particularly convenient:

$$
N(a+b\beta)=a^2+2b^2=|a+b\beta|^2.
$$

Consequently a nonzero element has magnitude at least 1. There's no extra factor of the field degree in the leading determinant estimate: the two complex embeddings have the same modulus. That is a better starting point than a generic norm estimate that treats the other embedding as an uncontrolled expense.

## What goes into the matrix?

Assume, for a contradiction, that $x$ has approximations $r_k=p_k/q_k$ with errors at most $q_k^{-\nu}$ for one fixed $\nu>2$ and arbitrarily large denominators. Choose finitely many, with successively well-separated weights $w_k=\lceil\log q_k\rceil$.

The centers are

$$
(\alpha^j,\beta jr_1,\ldots,\beta jr_m),\qquad 0\le j<K.
$$

Columns are monomials $Y^hX_1^{\gamma_1}\cdots X_m^{\gamma_m}$ of bounded weighted degree. Rows extract selected Taylor coefficients. If $G_k(t)$ is a sufficiently long polynomial truncation of $\log(1+t)$, an entry has the form

$$
[t^su^a]\,(\alpha^j(1+t))^h
\prod_k(\beta jr_k+G_k(t)+u_k)^{\gamma_k}.
$$

Here $[t^su^a]$ means “take that coefficient,” and the vector $a$ records the orders in the separate $u$ variables. You can think of the row as a derivative condition, with the factorials already divided out.

Weighted interpolation says that, for suitably chosen weights and sufficiently large height, the coefficient map is onto the row space. We can therefore choose a nonzero square minor $\Delta_H$ containing every row, where $H$ is the height controlling our degree bounds. The geometry behind this is substantial: weighted curve estimates, a blowup, and Serre vanishing. In this application those results establish independence of derivative conditions. A favorable count of rows and columns by itself wouldn't do it.

## What does clearing denominators actually cost?

Write $\alpha=U/D$. The factor $\alpha^{jh}$ stays in the matrix. Multiplying its column by $D^{Kh}$ turns it into

$$
U^{jh}D^{(K-j)h},
$$

which is integral in $\mathbb Z[\beta]$ because $j<K$. We also use column factors $\prod_kq_k^{\gamma_k}$ and row factors $\prod_kq_k^{-a_k}$, together with least-common-multiple factors clearing the coefficients of $G_k$.

Those negative row exponents are justified, not optimistic bookkeeping. The $u^a$ coefficient contains powers only up to $\gamma_k-a_k$, so that's how many denominator powers it really needs. The resulting entries have factors

$$
\prod_k(\beta jp_k+q_kG_k(t))^{\gamma_k-a_k},
$$

after coefficient extraction and multiplication by the logarithm-clearing factor. The cleared determinant is a nonzero element of $\mathbb Z[\beta]$, hence has magnitude at least 1.

If $M_H$ is the number of rows at height $H$, and $b_H$ is the average weighted row order $\sum_kw_ka_k$ divided by $H$, the lower bound reads

$$
\frac{\log|\Delta_H|}{M_HH}\ge -(1-b_H)-E_{\rm ar}.
$$

The parameter choice keeps $0\le b_H\le\theta<1$ and makes the arithmetic error $E_{\rm ar}$ small. I wouldn't throw away the $b_H$ saving: we're trying to reach every exponent above 2, and a coarser bound can lose the room needed for that conclusion.

## Where does the analytic saving come from?

The exact centers lie on the curve $z\mapsto(e^z,z,\ldots,z)$. Near them, use

$$
z_j(t)=j\beta x+\log(1+t).
$$

Then $e^{z_j(t)}=\alpha^j(1+t)$, and the discrepancy in the $k$th additive coordinate is

$$
\beta j(r_k-x)+G_k(t)-\log(1+t).
$$

This uses a local logarithm near 1. We never need to identify a principal logarithm of $\alpha^j$ with $j$ times a principal logarithm of $\alpha$ (which would be a poor way to keep track of multiple turns around the circle).

Taylor expansion gives two sources of smallness. Either many rows use low transverse indices, forcing repeated Taylor orders to vanish and surviving orders to be large; or many rows use high transverse indices, forcing enough factors of the tiny approximation errors. The first case is controlled by a collision estimate, the second by $q_k^{-\nu}$.

In the paper's notation this gives

$$
\frac{\log|\Delta_H|}{M_HH}
\le E_{\rm an}+o(1)+
\max\{-c_H,-\nu(A(1-\eta)-b_H)\},
$$

where $\theta<A<1$, $\eta>0$ is small, and $c_H$ tends to a constant we can make sufficiently large. Both alternatives must beat the arithmetic bound. The key positive gap is

$$
g=\nu(A(1-\eta)-\theta)-(1-\theta)>0.
$$

The parameter construction makes $E_{\rm ar}+E_{\rm an}<g$ and also makes the collision saving large enough. Since $b_H\le\theta$, the displayed gap is the worst case for the second alternative. We then fix all the fractions and parameters and let $H$ grow. The remaining $o(1)$ terms disappear, leaving incompatible bounds for the same nonzero determinant.

There is a new fixed cost here: multiplication by $\beta$ enlarges errors by $\sqrt2$. Bounding that by 2 produces a term $\log2/w_*$, where $w_*=\min_k w_k$. The proof explicitly reserves enough room for it by increasing the logarithm-denominator budget. It also retains the denominator cost from $D=3$ and the radius needed for the complex Taylor estimates. Small costs are still costs.

## What's left after the contradiction?

We have the eventual bound for $x=2y$. Given $\nu>2$, choose $2<\lambda<\nu$. Then, for sufficiently large $q$,

$$
|y-p/q|=\tfrac12|x-2p/q|
\ge\tfrac12q^{-\lambda}\ge q^{-\nu}.
$$

This proves the desired bound for $y$. It also proves irrationality: an exact rational value could be represented by unreduced fractions with unbounded denominators, violating the positive lower bound. Dirichlet then supplies the opposite inequality for the exponent.

The generic result stays within $\mathbb Q(\sqrt{-2})$ and non-torsion exponentials. Extending it to other quadratic fields, or to torsion periods such as $\pi/\sqrt d$, needs another argument. For the exact normalized number at the top, the needed conditions are all discharged in the paper.

*Casper initiated and directed the investigation. OpenAI coding agents contributed substantially to the mathematics, formal proof, verification tooling, and exposition. The paper credits OpenAI's inherited framework and Mathlib; the [verification record](../lean/VERIFICATION.md) documents the formal checks. External human peer review and an exhaustive priority claim are not asserted.*
