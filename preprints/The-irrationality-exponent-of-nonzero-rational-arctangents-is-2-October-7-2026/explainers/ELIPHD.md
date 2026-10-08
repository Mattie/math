# Rational arctangents: a guide for a PhD student outside Diophantine approximation

This explains Ryan Matthew Casper's *The irrationality exponent of nonzero rational arctangents is 2* (7 October 2026). The [paper PDF](../paper.pdf) and [manuscript](../build/manuscript.md) contain the complete argument and its source map. Here the aim is to make its mechanism and its dependencies legible to a mathematically mature reader who has not worked with interpolation determinants.

## What the theorem measures

For every rational $r\ne0$, the paper proves that the real number $x=\arctan r$, measured in radians, is irrational and has irrationality exponent $\mu(x)=2$. For an irrational $x$, this exponent is the supremum of the $\nu$ for which infinitely many reduced fractions satisfy

$$
0<|x-p/q|<q^{-\nu}.
$$

Dirichlet approximation supplies exponent 2. The work is in excluding every exponent above it. The actual endpoint is stronger in its quantifier presentation: for each $\nu>2$, there is a threshold $Q=Q(r,\nu)$ such that

$$
q\ge Q\quad\Longrightarrow\quad |\arctan r-p/q|\ge q^{-\nu}
$$

for all integer $p,q$, including unreduced fractions. This also proves irrationality, since an exact rational value would admit exact representations with unbounded denominators.

The threshold may deteriorate as $\nu\downarrow2$. There is no conclusion here of the form $|x-p/q|\ge c/q^2$ with one positive constant $c$. That is the stronger condition of bad approximability. Nor does the endpoint provide a practical numerical threshold. A computation of continued fractions, however long, cannot replace the eventual bound.

## The inherited argument and the new input

The foundation is OpenAI's [*The irrationality exponent of π is 2*, dated 24 September 2026](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026), cited at the pinned revision used by this package. Its weighted logarithmic interpolation and determinant method joins a geometric rank theorem to incompatible arithmetic and analytic estimates for one determinant. The released library supplies substantial geometric comparison and collision estimates.

Casper's preceding [positive-rational-logarithm preprint](../../The-irrationality-exponent-of-positive-rational-logarithms-is-2-October-7-2026/README.md) generalized the interpolation geometry to distinct exponential coordinates and retained the additional costs for a rational base. For $x=\log a$, with positive rational $a\ne1$, the relevant coordinates are $a^j=e^{jx}$. This arctangent paper uses that generalized geometry and its complex analytic interfaces. It does not rebuild the whole framework from elementary approximation theory.

Set

$$
\vartheta=2\arctan r,\qquad
\alpha=e^{i\vartheta}=\frac{1+ir}{1-ir}
=\frac{1-r^2}{1+r^2}+i\frac{2r}{1+r^2}.
$$

The angle is specified directly. There is no assumption that a principal logarithm satisfies $\log(\alpha^j)=ij\vartheta$. For $r=1/2$, the exact base is $(3+4i)/5$, so the arithmetic belongs to $\mathbb Q(i)$, with denominator $D=5$. More generally write $\alpha=U/D$, $U\in\mathbb Z[i]$, $D>0$. A reduced representation is unnecessary.

The interpolation centers need distinct powers of $\alpha$. A root of unity with rational real and imaginary parts must be one of $1,-1,i,-i$: its doubled coordinates are rational algebraic integers, hence integers, and their squares sum to 4. Substituting the displayed coordinates leaves exactly $r=0,\pm1$. Zero is excluded by the theorem; $\pm1$ are handled using $\arctan(\pm1)=\pm\pi/4$ and the inherited π bound. The final family theorem therefore has no non-torsion hypothesis left over.

## Why interpolation is a substantive step

Suppose exceptionally good approximations $p_k/q_k$ to $\vartheta$ occur at arbitrarily large denominators. Choose finitely many with successively separated $w_k=\lceil\log q_k\rceil$. At the centers

$$
(Y,X_1,\ldots,X_m)=(\alpha^j,ij p_1/q_1,\ldots,ij p_m/q_m)
$$

use local coordinates $t=Y/\alpha^j-1$ and $u_k=X_k-ij p_k/q_k-\log(1+t)$. Weights restrict both polynomial degree and the local Taylor coefficients, or jets, to be prescribed.

The geometric theorem says that bounded weighted-degree polynomials surject onto those jet packets at sufficiently large heights $H=nR$. This supplies full row rank and a nonzero square minor. Counting coefficients alone would not establish surjectivity. An unrestricted Chinese remainder theorem would not supply the required degree bound either.

The manuscript obtains that bound through a curve estimate, inherited persistent normal comparison, and an ordinary blowup. A residue argument uses the impossibility of $dX=dY/Y$ for nonconstant rational $Y$ on a complete curve. Distinct $Y$-coordinates ensure that a constant-$Y$ curve meets at most one center. An explicit positive combination of a nef divisor and an ample divisor establishes the needed ampleness; the argument does not identify strict nefness with ampleness. Eventual direct-image statements and Serre vanishing then produce the bounded-degree interpolation. These are substantial algebraic-geometric inputs, even though the target theorem concerns a familiar real function.

## The same determinant on both sides

A typical entry is

$$
[t^su^\beta]\,(\alpha^j(1+t))^h
\prod_k(ij p_k/q_k+G_k(t)+u_k)^{\gamma_k},
$$

where $G_k$ truncates the series for $\log(1+t)$. The factor $\alpha^{jh}$ remains in the matrix. Its modulus being one does not authorize deleting it: doing so would change the interpolation problem and the determinant.

Arithmetic clears this entry by multiplying its column by $D^{Kh}\prod q_k^{\gamma_k}$, its row by $\prod q_k^{-\beta_k}$, and every entry by an appropriate product of least common multiples. The exact identity

$$
D^{Kh}\alpha^{jh}=U^{jh}D^{(K-j)h}
$$

puts the cleared entries in $\mathbb Z[i]$. The nonzero cleared determinant $Z$ has $|Z|\ge1$, because $|Z|^2$ is a positive integer. There is no extra factor of two in the exponent cost merely because the number field has degree two.

The row divisions are legitimate savings: extracting $u^\beta$ reduces the powers whose denominators need clearing. If $M_H$ is the row count and $b_H$ the normalized mean row weight, arithmetic gives

$$
\frac{\log|\Delta_H|}{M_HH}\ge -(1-b_H)-E_{\rm ar},
\qquad 0\le b_H\le\theta<1.
$$

Here $\theta$ is the paper's weight parameter, unrelated to the angle $\vartheta$. In particular $E_{\rm ar}$ includes $K\log D/w_0$. Dropping the row savings changes the leading bound; ignoring $D$ omits a genuine cost.

Analysis compares the approximate centers with $z_j(t)=ij\vartheta+\log(1+t)$. The discrepancy is $ij(p_k/q_k-\vartheta)$, plus the truncation tail. Multiplication by $i$ preserves the approximation error's magnitude. Expanding entire functions $e^{hz}z^d$ then exposes a determinant cancellation: two rows with the same transverse index and Taylor order give zero. Surviving terms must either use many separated Taylor orders or pay for sufficiently high transverse indices through the tiny approximation errors. This is the collision alternative versus the approximation-error alternative.

## Where the exponent 2 enters

For $\nu>2$, parameters can be chosen with

$$
0<\theta<A<B<1,\qquad \nu(A-\theta)>1-\theta,
\qquad CB<1<B^{-1}C\theta.
$$

Set $K=\lfloor C^m\rfloor$, $w_0=B^{-m}$, and $v_0=2K\theta^mw_0$. Increasing $m$ makes $K/w_0\to0$ and $m/v_0\to0$, while the collision saving grows like $(B/A)^m/(m+1)$. Thus both the Gaussian denominator cost and the complex analytic radius cost, respectively $K\log D/w_0$ and $\rho K/w_0$, become small.

The order of choices matters. Fix the target angle and $\nu$, choose the auxiliary parameters and one finite dimension, select separated approximants, and only then send the interpolation height $H=nR\to\infty$. Both analytic alternatives become incompatible with the arithmetic lower bound. The paper does not obtain the endpoint by putting $\nu=2$ into a strict inequality.

Finally transport the bound from $x=\vartheta$ to $x/2$. Given $\nu>2$, choose $2<\lambda<\nu$. Then

$$
\left|x/n-p/q\right|=n^{-1}|x-np/q|
\ge n^{-1}q^{-\lambda}\ge q^{-\nu}
$$

eventually, for $n=2$, or $n=4$ in the π exceptions. Negation is immediate. This explicit rational scaling is sufficient. An invariance principle for arbitrary algebraic scaling would be unjustified.

## What was checked

The [verification record](../lean/VERIFICATION.md) reports compilation in Lean 4.34.1, a transitive axiom audit allowing exactly `propext`, `Classical.choice`, and `Quot.sound`, acceptance of the exported proof by Nanoda, and replay in a second stock Lean 4.34.0 kernel. Negative controls tested rejection of an extra axiom and an ill-typed fixture. These checks concern the stated formal endpoints and their dependency closure. This explanation has not rerun those builds.

Casper initiated and directed the investigation. OpenAI coding agents contributed substantially to the argument, Lean proofs, verification, and exposition. OpenAI's method and library, Mathlib, and the preceding rational-logarithm implementation remain substantial dependencies. Neither automated acceptance nor this explanatory account constitutes external human peer review. The paper makes no exhaustive priority claim. Its [formal endpoint](../lean/Arctangent/Main.lean) and manuscript source map are the places to inspect the exact theorem and the inherited proof boundary.
