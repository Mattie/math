# The normalized quadratic arctangent: a guide to the determinant proof

Ryan Matthew Casper's [paper](../paper.pdf), dated 7 October 2026, proves

$$
\mu\!\left(\frac{\arctan\sqrt2}{\sqrt2}\right)=2.
$$

The [manuscript](../build/manuscript.md) gives the full argument. This guide assumes graduate mathematics, but not prior experience with irrationality measures or weighted logarithmic interpolation. I'll emphasize what the construction needs from geometry, where the quadratic arithmetic enters, and why the normalization cannot be dropped.

## The exact statement

For irrational real $z$, the rational irrationality exponent $\mu(z)$ is the supremum of the exponents $\nu$ admitting infinitely many distinct reduced rational approximants $p/q$, with $q\ge2$, such that

$$
0<|z-p/q|<q^{-\nu}.
$$

The main approximation theorem, for $y=\arctan(\sqrt2)/\sqrt2$, is

$$
\forall\nu>2\;\exists Q\in\mathbb Z,\ Q\ge2:
\quad\forall p,q\in\mathbb Z,\ q\ge Q
\Longrightarrow |y-p/q|\ge q^{-\nu}.
$$

The fractions here need not be reduced. This proves irrationality directly, since a rational $y$ would admit exact representations with unbounded denominators. Dirichlet then supplies exponent 2 from below, and the eventual bound excludes every larger exponent. Neither a finite decimal computation nor a convention for an unbounded supremum is doing work here.

The quantifier order is essential. $Q$ depends on $\nu$; the theorem doesn't give bad approximability, which would require a fixed $c>0$ with $|y-p/q|\ge c/q^2$ for all relevant fractions.

## Arithmetic input and scope

Put $\beta=i\sqrt2$ and $\mathcal O=\mathbb Z[\beta]$. The generic result starts from a nonzero real $x$, a positive integer $D$, and $U\in\mathcal O$ satisfying

$$
\alpha=U/D=e^{\beta x},\qquad
\alpha^0,\alpha^1,\ldots\text{ pairwise distinct}.
$$

Equivalently, the exponential is a non-torsion point in $\mathbb Q(\sqrt{-2})$. Here “non-torsion” means it is not a root of unity. This is a statement about the chosen real logarithmic parameter $x$; no principal branch of a global logarithm is selected.

For the concrete application,

$$
x=2y,\qquad U=-1+2\beta,\qquad D=3.
$$

The double-angle formulas verify $e^{\beta x}=(-1+2\beta)/3$. Its trace is $-2/3$. If $\alpha$ were a root of unity, $\alpha$ and $\bar\alpha$ would be algebraic integers, making their rational sum an integer. The trace excludes this, and $\alpha\ne0$ then gives distinct powers.

After proving the bound for $x$, rational division by 2 proves it for $y$. The factor $\sqrt2$ is already built into the exponential and the approximation variable. General algebraic scaling does not preserve irrationality exponents automatically; it needn't preserve irrationality at all. Thus no conclusion about $\mu(\arctan\sqrt2)$ follows from this theorem. The formal generic result is confined to this quadratic field and non-torsion inputs, with no assertion for arbitrary imaginary quadratic fields or torsion periods such as $\pi/\sqrt d$.

## Which parts are inherited?

OpenAI's [paper and library for the irrationality exponent of $\pi$](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026) supply the weighted interpolation and determinant framework. Casper's preceding [rational-logarithm adaptation](../../The-irrationality-exponent-of-positive-rational-logarithms-is-2-October-7-2026/README.md) treats nonzero logarithms of positive rational numbers, using rational exponential coordinates. His [rational-arctangent adaptation](../../The-irrationality-exponent-of-nonzero-rational-arctangents-is-2-October-7-2026/README.md) moves to Gaussian arithmetic and distinguishes non-torsion centers from the exceptions handled by the $\pi$ result.

The present extension changes the order used for clearing denominators, its embedding and modulus bound, the approximation-center rotation, and the budget that pays for that rotation. Nonzero-minor geometry, the collision estimate, parameter-existence machinery, and the final irrationality-exponent implication remain substantial inherited results. It would be misleading to describe the work as a fresh proof of those inputs.

## What interpolation has to provide

Fix $\nu>2$ and suppose $x$ admits approximations $r_k=p_k/q_k$ of error at most $q_k^{-\nu}$ with arbitrarily large denominators. We will choose only finitely many of them. Write

$$
w_k=\lceil\log q_k\rceil,\qquad v_k=w_k/\theta,\qquad
T_k=\lceil F_0w_k/v_0\rceil,
$$

where $0<\theta<1$ and $F_0>2/\theta$, and set

$$
G_k(t)=\sum_{1\le l<T_k}\frac{(-1)^{l+1}}l t^l.
$$

Columns are monomials $Y^hX^\gamma$ satisfying

$$
w_0h+\sum_kw_k\gamma_k\le H,
$$

and rows are triples $(j,s,a)$ satisfying

$$
0\le j<K,\qquad v_0s+\sum_kv_ka_k<H.
$$

Here $a,\gamma$ are vectors of nonnegative integer exponents, and $[t^su^a]$ extracts the indicated Taylor coefficient. The coefficient matrix is

$$
[t^su^a]\,(\alpha^j(1+t))^h
\prod_k(\beta jr_k+G_k(t)+u_k)^{\gamma_k}.
$$

A jet is just the finite list of Taylor coefficients being prescribed at a point. The weighted interpolation theorem says that the polynomial-to-jet map is surjective, once the rational weights satisfy strict volume and coordinate inequalities and suitable product-separation conditions. It applies at distinct nonzero multiplicative centers with arbitrary complex additive coordinates. Thus the complex centers above are allowed.

For a reader outside algebraic geometry, the role of its machinery is quite specific. Curve comparison controls the permitted weighted vanishing; a blowup encodes vanishing conditions geometrically; and Serre vanishing removes the cohomological obstruction to surjectivity at large height. These are proofs of independence, not a count of nominal degrees of freedom. The polynomial truncations preserve the requested jets because $T_kv_0\ge F_0w_k>v_k$.

At sufficiently large heights in a cofinal sequence $H=nR$, with $R$ clearing the rational weights, choose a square nonzero minor $\Delta_H$ using every row. Let $M_H$ be the row count and put

$$
b_H=\frac{\sum_{\rm rows}\sum_kw_ka_k}{M_HH}.
$$

Then $0\le b_H\le\theta$, and lattice counting gives

$$
M_H\sim\frac{K\theta^mH^{m+1}}{(m+1)!v_0\prod_kw_k}.
$$

Both subsequent estimates concern this same minor, uniformly over the selected columns.

## Clearing into the quadratic order

The useful arithmetic fact is elementary:

$$
N(a+b\beta)=a^2+2b^2=|a+b\beta|^2,
\qquad a,b\in\mathbb Z.
$$

A nonzero element of $\mathcal O$ therefore has modulus at least 1. There is no field-degree penalty in the leading term of the lower bound: conjugation preserves complex modulus, and the norm identity already controls the selected embedding.

Let $L_k=\operatorname{lcm}(1,\ldots,T_k)$ and

$$
E_H=\prod_kL_k^{\lfloor H/w_k\rfloor}.
$$

Multiply column $(h,\gamma)$ by $D^{Kh}\prod_kq_k^{\gamma_k}$, row $(j,s,a)$ by $\prod_kq_k^{-a_k}$, and every entry by $E_H$. When $a\le\gamma$, the cleared entry is

$$
E_HU^{jh}D^{(K-j)h}\binom\gamma a
[t^s](1+t)^h
\prod_k(\beta jp_k+q_kG_k(t))^{\gamma_k-a_k}.
$$

Otherwise it is zero. All these entries belong to $\mathcal O$: $j<K$ makes the exponent of $D$ nonnegative, and the powers of $L_k$ clear the logarithm coefficients. The cleared determinant is nonzero, since every scaling factor is nonzero.

Notice both the exponential factors and the negative row exponents. Deleting $\alpha^{jh}$ would change the actual matrix. Discarding the row savings would weaken the leading arithmetic estimate. I find the latter particularly consequential: the derivative order tells us which powers of $q_k$ have already disappeared, and paying for them again can prevent the final estimate from reaching 2.

With $\Lambda=4+\log4$ and $w_*=\min_kw_k$, the result is

$$
\frac{\log|\Delta_H|}{M_HH}\ge-(1-b_H)-E_{\rm ar},
$$

where

$$
E_{\rm ar}=\frac{\Lambda F_0m}{v_0}
+\Lambda\sum_k\frac1{w_k}+\frac\theta{w_*}
+\frac{K\log D}{w_0}.
$$

The last term is the cost of the base denominator $D$, which is 3 in the concrete application.

## The analytic upper bound

Set $\omega=\beta x$ and $\rho=100\max(1,2|x|)$. On $|t|<1$, use

$$
z_j(t)=j\omega+\log(1+t).
$$

Then $e^{z_j(t)}=\alpha^j(1+t)$ and the additive coordinates are

$$
z_j(t)+u_k+e_{jk}+\tau_k(t),\qquad
e_{jk}=\beta j(r_k-x),\quad
\tau_k=G_k-\log(1+t).
$$

Only the local logarithm of $1+t$ appears (there is no branch identity for $\log(\alpha^j)$ hiding in this step).

Expand the column functions along the curve:

$$
f_{b,P}(z)=[u^b]P(e^z,z+u_1,\ldots,z+u_m)
=\binom\gamma b e^{hz}z^{|\gamma|-|b|}.
$$

Here $b\le\gamma$ coordinatewise; otherwise the coefficient function is zero.

A row expansion with transverse index $b\ge a$ has scalar size bounded by

$$
\exp\{-\nu w(b-a)+HE_{\rm tr}\},
\qquad w(b-a)=\sum_kw_k(b_k-a_k),
$$

with

$$
E_{\rm tr}=\frac\nu{F_0}+\frac{\log2}{v_0}
+\frac{\log4+\log(2K)+\nu+\log2}{w_*}.
$$

The extra $\log2/w_*$ pays for $|\beta|=\sqrt2\le2$. It is a small term, but it must be included.

Taylor expansion on a larger disc bounds the holomorphic part with error

$$
E_{\rm hol}=\frac{\rho K}{w_0}+\frac{\log2}{v_0}
+\frac{\log(2\rho K)}{w_*}.
$$

The determinant provides additional decay. If two rows with the same transverse index select the same Taylor order, their contribution vanishes. For $n_b$ rows with that index, surviving Taylor orders have sum at least $\binom{n_b}{2}$. This is the collision saving.

Split according to whether at least $\eta M_H$ rows have transverse weight at most $AH$. In that case, Cauchy–Schwarz turns collisions into a normalized saving $c_H$, where

$$
c_H\longrightarrow c_\infty
=\frac{c\eta^2K\theta^m}{(m+1)v_0A^m},
\qquad c=\frac{\log2}{4}.
$$

Otherwise the large transverse indices force enough approximation-error factors to save $\nu(A(1-\eta)-b_H)$. The finite expansion count and remaining collision terms contribute $o(1)$ after normalization. Thus, with $E_{\rm an}=E_{\rm tr}+E_{\rm hol}$,

$$
\frac{\log|\Delta_H|}{M_HH}
\le E_{\rm an}+o(1)+
\max\{-c_H,-\nu(A(1-\eta)-b_H)\}.
$$

## How the parameter choice reaches every $\nu>2$

Choose positive rational parameters satisfying

$$
0<\theta<A<B<1,\quad
\nu(A-\theta)>1-\theta,\quad
C>1,\quad CB<1,\quad B<C\theta<1.
$$

The interval behind this choice explains the threshold 2. Choose rational $b\in(1/2,1-1/\nu)$, then take $\theta=1-s$ and $A=1-bs$ for small positive rational $s$. The inequality $A^2<\theta$ permits the remaining choices of $B,C$. Such a $b$ exists exactly when $\nu>2$.

Choose small $\eta>0$ so that

$$
g=\nu(A(1-\eta)-\theta)-(1-\theta)>0,
$$

then choose $F_0$ large. Increasing $m$, set

$$
K=\lfloor C^m\rfloor,\qquad w_0=B^{-m},\qquad
v_0=2K\theta^mw_0.
$$

Now $K/w_0\to0$, $v_0\to\infty$, $m/v_0\to0$, and

$$
c_\infty=\frac{c\eta^2(B/A)^m}{2(m+1)}\longrightarrow\infty.
$$

The weighted interpolation volume is exactly $K(w_0/v_0)\theta^m=1/2$. Strict coordinate and product conditions can also be arranged. Only after fixing these parameters do we choose the approximants, with all $w_k$ sufficiently large and successively separated. Finally we send $H$ to infinity. This order keeps the interpolation threshold from becoming a circular requirement on the approximants.

For the new rotation term, replace the lcm budget constant by $\Lambda'=\Lambda+\log2$. Since the minimum weight is attained,

$$
\frac{\log2}{w_*}\le\log2\sum_k\frac1{w_k}
\le(\Lambda'-\Lambda)
\left(\frac{F_0m}{v_0}+\sum_k\frac1{w_k}\right).
$$

This pays for the new term within the parameter budget. The construction retains both $\rho K/w_0$ and $K\log D/w_0$ and gives

$$
E_{\rm ar}+E_{\rm an}<g,\qquad
c_\infty>1+E_{\rm ar}+E_{\rm an}.
$$

The collision alternative now contradicts the lower bound. In the other alternative, the difference between the two leading costs is

$$
\nu(A(1-\eta)-b_H)-(1-b_H)\ge g,
$$

because $b_H\le\theta$ and $\nu>1$. That contradicts the same lower bound once $H$ is large. Hence the assumed approximations cannot occur with unbounded denominators.

## Returning to the normalized target

To transfer the eventual bound from $x$ to $x/2$, fix $\nu>2$ and choose $2<\lambda<\nu$. For all sufficiently large $q$,

$$
|x/2-p/q|=\tfrac12|x-2p/q|
\ge\tfrac12q^{-\lambda}\ge q^{-\nu}.
$$

The exponent gap absorbs the rational factor. Applying this to the explicitly constructed $x$ proves the approximation theorem for $y$, and irrationality plus Dirichlet completes $\mu(y)=2$.

The [verification record](../lean/VERIFICATION.md) identifies the exact Lean statements and accepted independent proof replays. They concern the specified formal statements and their foundational axioms, not external human review or an exhaustive priority determination. In particular, the concrete endpoint carries no unproved arithmetic, interpolation, or determinant premise.

*Ryan Matthew Casper initiated and directed the investigation. OpenAI coding agents contributed substantially to the mathematical adaptation, Lean proof development, verification tooling, and exposition. The paper attributes the inherited mathematical framework and library to OpenAI, alongside Mathlib and Casper's preceding adaptations.*
