# Paired affine logarithms: a proof memo

This memo gives a mathematical argument for the following three real numbers:

```math
x_1=\log 2+\sqrt2,\qquad x_2=\sqrt2\log2,\qquad
x_3=\frac{\log(3+2\sqrt2)}{\sqrt2}+\sqrt3.
```

For each number, the conclusion is irrationality and irrationality exponent at most four. The quantitative statement proved is stronger than just the exponent assertion: for every real $`\nu>4`$, there exists an integer $`Q\ge2`$ such that

```math
q^{-\nu}\le |x-p/q|\quad(p\in\mathbb Z,\ q\in\mathbb N,\ q\ge Q).
\qquad\text{(1)}
```

The fractions in (1) need not be reduced. The threshold can depend on the number and on $`\nu`$. No bound at $`\nu=4`$, explicit numerical threshold, or equality of the exponent with four is asserted.

Source references below are relative to the package root. Namespace prefixes are `OAI` unless otherwise indicated. This argument invokes the inherited weighted interpolation and analytic collision theorems specified below; it does not reprove their algebraic geometry or complex analysis foundations. Its purpose is to expose their interfaces and the deduction from them, including the constants that survive normalization.

## 1. A common field-theoretic statement

Let $`F`$ be a number field of degree four. Let $`a,u,v\in F`$ be algebraic integers. Suppose one embedding $`\sigma_0:F\hookrightarrow\mathbb C`$ sends $`a`$ to a positive real number $`b_0\ne1`$. Let $`x\in\mathbb R\setminus\{0\}`$. Suppose there is a set $`G`$ of exactly two distinct embeddings such that

```math
\exp(\sigma(u)(x-\sigma(v)))=\sigma(a),\qquad
|\sigma(u)|\le2\quad(\sigma\in G).
\qquad\text{(2)}
```

Then (1) holds for $`x`$. This is the statement of `PairedAffine.Endpoint.paired_eventualLowerBound` in `PairedAffine/Endpoint.lean`. The distinguished embedding need not be stipulated to lie in $`G`$. No compatibility identity is required at the other embeddings.

There are four complex embeddings, counted separately even when particular elements have repeated images. Put

```math
\kappa=\sum_\sigma\log\max(1,|\sigma(a)|),\quad
R=\sum_\sigma |\sigma(u)|(|x|+1+|\sigma(v)|),\quad R'=2R+2,
```

```math
\rho=100\max\left(1,|x|,\sum_\sigma|\sigma(u)(x-\sigma(v))|\right).
\qquad\text{(3)}
```

These are fixed before selecting approximation data. They give nonnegative $`\kappa,R`$, $`\rho\ge100`$, $`100|x|\le\rho`$, and the separate bound $`100|\sigma(u)(x-\sigma(v))|\le\rho`$ at every embedding. The notation `proxy = exp x` in the source merely supplies $`\log(\mathrm{proxy})=x`$ to logarithmic data structures. It is not the algebraic base $`a`$, nor is it required to be algebraic.

Fix $`\nu>4`$ and suppose, for contradiction, that approximations with

```math
|x-p/q|\le q^{-\nu}
\qquad\text{(4)}
```

exist with unbounded positive denominators. All constants and finite approximation data chosen next remain fixed when a later height $`H`$ tends to infinity.

## 2. Parameter construction and its precise margins

Write $`\Lambda=\log4+4`$ and $`c=\log2/4`$. The first constant bounds logarithms of least common multiples; the second is the analytic collision constant. The interface `AlgebraicLog.exists_admissible_parameters` in `AlgebraicLog/AdmissibleParameters.lean` takes real $`x,\nu,\Lambda,c,\rho,\delta,\kappa,R'`$, with $`\nu>4`$, $`\Lambda,c>0`$, $`x\ne0`$, $`\rho\ge100`$, $`100|x|\le\rho`$, and $`\delta,\kappa,R'\ge0`$, together with precisely the unbounded-denominator hypothesis (4). Here $`\delta=0`$ because the algebraic base is integral.

Its construction first chooses rational shape parameters

```math
0<\theta<A<B<1,\quad C>1,\quad B<1/C,\quad B<C\theta<1,
```

and $`0<\eta<1`$, so that

```math
g=\nu(A(1-\eta)-\theta)-2(1-\theta)>0.
\qquad\text{(5)}
```

This is `AlgebraicLog.ParameterShape.exists_quadratic_shape`, obtained by applying `PiExponent.exists_parameters` at exponent $`\nu/2>2`$; the approximations themselves retain exponent $`\nu`$. Choose $`0<\epsilon<g`$, $`\epsilon\le1/2`$; then choose $`F_0>2/\theta`$ sufficiently large that $`\nu/F_0<\epsilon/3`$. Next choose dimension $`m\ge1`$, and set

```math
K=\lfloor C^m\rfloor,\quad w_0=B^{-m},\quad
v_0=2K\theta^m w_0.
\qquad\text{(6)}
```

Thus $`K(w_0/v_0)\theta^m=1/2`$, and $`K\theta^m<1`$. The dimension budget gives both a small error margin and a collision limit exceeding three. Small positive rational $`\sigma`$ is then chosen with

```math
(1+3\sigma)^{m+1}/2<1,\quad
(1+3\sigma)^mK\theta^m<1,\quad(1+\sigma)\theta<1.
```

Only after this is a sufficiently large initial weight selected, and (4) supplies successive approximations with arbitrarily separated logarithmic weights. The first $`m`$ are denoted $`p_i/q_i`$, with $`q_i\ge2`$, $`p_i\ne0`$, and
$`w_i=\lceil\log q_i\rceil\ge1`$. Set $`w_*=\min_i w_i>0`$. Separation can be imposed because (4) permits each next denominator to exceed any already determined threshold. The construction uses `Logarithm.exists_normalized_successive_approximations`; it does not infer separation from mere distinctness of denominators.

The exact error quantities needed below are

```math
E=\frac{\Lambda F_0m}{v_0}+\Lambda\sum_iw_i^{-1}+\frac\theta{w_*},
```

```math
U(S)=\frac{\log2}{v_0}+\frac{\kappa K+\log(3/2)}{w_0}
       +\frac{\log(2(KS+2))}{w_*},
```

```math
T=\frac\nu{F_0}+\frac{\log2}{v_0}
 +\frac{\log4+\log(2K)+\nu}{w_*},\quad
J=\frac{\rho K}{w_0}+\frac{\log2}{v_0}
 +\frac{\log(200K)+\log(\rho/100)}{w_*},\quad V=T+J.
\qquad\text{(7)}
```

The dimension and weight margins in `AdmissibleParameters` prove

```math
2E+U(R')+V<g,\qquad
2+2E+U(R')+V<C_\infty,
\qquad\text{(8)}
```

where

```math
C_\infty=c\frac{\eta^2K\theta^m}{(m+1)v_0A^m}>3.
```

These are `error_sum_lt_gap` and `collision_exceeds_error_sum`. They are genuine output inequalities of the parameter construction. In particular the order is shape, initial scale, dimension, rational slack, initial approximation weight, finite approximations, and finally height; no parameter is adjusted after a minor is selected.

The dimension choice is supported by concrete limiting ratios, not by assuming that arbitrary errors can be made small simultaneously. With the shape fixed, $`K/w_0`$ tends to zero since $`CB<1`$, while $`v_0`$ grows exponentially since $`C\theta/B>1`$; the floor in $`K`$ does not change these limits. Thus the terms with denominators $`v_0,w_0`$, including $`F_0m/v_0`$, tend to zero. Meanwhile the collision limit simplifies to $`c\eta^2(B/A)^m/(2(m+1))`$, which tends to infinity because $`B>A`$. These are the competing requirements discharged by `AlgebraicLog.exists_quadratic_dimension_budget` in `AlgebraicLog/DimensionBudget.lean`. After dimension is fixed, the remaining terms in (7) are bounded by a constant times $`1/w_*`$, since $`\sum_i1/w_i\le m/w_*`$. The arbitrary initial denominator threshold in (4) makes this last error small. This explains why the dimension is chosen before the approximations, and why increasing height alone would not remove those fixed errors.

## 3. The matrix and the inherited interpolation input

For $`H>0`$, take columns $`(h,\gamma)\in\mathbb N\times\mathbb N^m`$ satisfying
$`w_0h+\sum_iw_i\gamma_i\le H`$, and rows $`(j,s,\beta)`$ with $`0\le j<K`$ and
$`v_0s+\sum_i(w_i/\theta)\beta_i<H`$. Let $`M`$ be the number of rows. Put
$`T_i=\lceil F_0w_i/v_0\rceil`$ and
$`L_i(t)=\sum_{1\le k<T_i}(-1)^{k+1}t^k/k`$.
At embedding $`\sigma`$, define $`z_\sigma=\sigma(a)`$ and
$`r_{\sigma i}=\sigma(u)(p_i/q_i-\sigma(v))`$. The matrix entry is

```math
z_\sigma^{jh}[t^s Z^\beta]
 (1+t)^h\prod_i(Z_i+jr_{\sigma i}+L_i(t))^{\gamma_i}.
\qquad\text{(9)}
```

This is `PairedAffine.matrix` in `PairedAffine/Data.lean`, using the inherited `InterpolationMatrix.entry`. In particular the factor $`z_\sigma^{jh}`$ is part of the matrix.

The decisive geometric input is `Logarithm.eventually_weighted_logarithmic_interpolation` in `Logarithm/Interpolation.lean`. Its input `GeometryData` is fully numerical except for centers: positive rational degree weights $`d_i`$, positive rational jet weights $`e_i`$, positive rational $`\sigma`$, distinct nonzero complex multiplicative centers $`Y_j`$, and arbitrary complex additive centers $`c_{ji}`$. Its hypotheses are

```math
K(1+3\sigma)^{m+1}\frac{\prod_{i=0}^m d_i}{\prod_{i=0}^m e_i}<1,
\qquad (1+\sigma)d_i<e_i\ (i>0),
\qquad\text{(10)}
```

and the following separated-product condition. For equal-cardinality subsets $`P,Q\subseteq\{0,\ldots,m\}`$, if $`i>0`$ belongs to $`P\setminus Q`$ and membership in $`P,Q`$ agrees above $`i`$, then

```math
D_m(\sigma)\prod_{j\in Q}e_j<\prod_{j\in P}d_j,
\quad D_m(\sigma)=2(m+2)^{m+2}(1+(m+2)/\sigma)^{m+2}.
\qquad\text{(11)}
```

The conclusion is surjectivity, at all sufficiently large integers $`n`$, of the coefficient-packet map of polynomials of weighted degree at most $`n\mathcal R`$ onto all formal logarithmic jet packets of jet weight strictly below $`n\mathcal R`$ at those centers. Here $`\mathcal R>0`$ is the rational geometric scale constructed from the data. The formal coordinates are $`Y=Y_j(1+t)`$, $`X_i=c_{ji}+\log(1+t)+Z_i`$. This is a deep inherited theorem, obtained in the source through ampleness of an interpolation bundle and eventual jet restriction. Those foundations are invoked here, not established anew.

Apply it with degree weights $`(w_0,w_i)`$, jet weights $`(v_0,w_i/\theta)`$, $`Y_j=b_0^j`$, and $`c_{ji}=jr_{\sigma_0i}`$. Positive $`b_0\ne1`$ makes these power centers distinct and nonzero. Equations (10)–(11) follow from the admissible volume, slack, and separated-weight construction (`AlgebraicLog/CurveWeights.lean`, `AlgebraicLog/ApproximationGeometry.lean`). Additive centers have no further hypothesis. Because $`T_iv_0\ge w_i/\theta`$, the substitution that replaces each formal logarithm by its truncation is invertible and preserves the weighted filtration. It therefore preserves surjectivity of the coefficient-packet map; individual coefficients need not be equal. This is `Logarithm.ScaledTruncation.formalLog_packets_surjective_iff_truncated`. The formal-to-matrix interface is `Logarithm.ScaledMatrix.truncatedLogMatrix_surjective_of_formalLog_packets`, used in `PairedAffine.Geometry.cofinal_matrix`.

Consequently, for every lower height bound there is a larger $`H=n\mathcal R`$ at which (9) for $`\sigma_0`$ has full row rank. Choose a nonzero full-row minor, hence one column selection $`s_H`$. Keep this exact selection at all embeddings and denote its determinants by $`\Delta_\sigma`$. No later estimate chooses a different minor.

## 4. Integral clearing and the norm comparison

For a selected column $`\gamma`$, set $`e_i=\lfloor H/w_i\rfloor`$, so $`\gamma_i\le e_i`$. Put $`D_i=\mathrm{lcm}(1,\ldots,T_i)`$. The positive rational clearing scalar is

```math
\mathcal C=\left(\prod_iD_i^{e_i}\right)^M
  \left(\prod_{\text{rows }r}\prod_iq_i^{-\beta_{ri}}\right)
  \left(\prod_{\text{selected columns }c}\prod_iq_i^{\gamma_{ci}}\right).
\qquad\text{(12)}
```

It need not be an integer. Define integral affine numerators
$`n_i=u(p_i-q_iv)\in\mathcal O_F`$. For an entry with $`\beta\le\gamma`$, multiplication by its row and column factors replaces each shifted logarithm by the integral-coefficient polynomial
$`D_i(jn_i+q_iL_i(t))`$, raised to exponent $`\gamma_i-\beta_i`$; spare powers of $`D_i`$ remain integral. Binomial coefficients and the factor $`a^{jh}`$ are integral. If some $`\beta_i>\gamma_i`$, the entry vanishes. Thus the scaled entries are embeddings of entries of one matrix over $`\mathcal O_F`$. Its determinant $`Z`$ satisfies

```math
\sigma(Z)=\mathcal C\Delta_\sigma\quad\text{for every }\sigma.
\qquad\text{(13)}
```

This is `PairedAffine.Arithmetic.exists_integral_entry_lift` in `PairedAffine/ArithmeticClearing.lean` and `PairedAffine.Arithmetic.exists_integral_selected_minor` in `PairedAffine/Arithmetic.lean`. Since $`\Delta_{\sigma_0}\ne0`$, $`Z\ne0`$; injectivity of every field embedding then gives $`\Delta_\sigma\ne0`$ for every $`\sigma`$. This is why all logarithms below are legitimate.

Set

```math
b_H=\frac{\sum_{\text{rows }r}\sum_iw_i\beta_{ri}}{MH},
\qquad 0\le b_H\le\theta.
```

The inherited least-common-multiple estimate, column degree bound, and inverse row factors in (12) give

```math
\log\mathcal C\le MH(1-b_H+E).
\qquad\text{(14)}
```

The exact reference is `PairedAffine.Arithmetic.log_selectedScalar_le`, using `AlgebraicLog.SelectedArithmetic` with base denominator one. Dropping the inverse row factors would lose the $`-b_H`$ term and would not reproduce this argument.

The nonzero algebraic integer $`Z`$ has nonzero integer norm, so
$`1\le\prod_\sigma|\sigma(Z)|`$. By (13),

```math
0\le4\log\mathcal C+\sum_\sigma\log|\Delta_\sigma|.
\qquad\text{(15)}
```

If the two good normalized logarithms are at most $`B_H`$ and the other two at most $`D_H`$, then (14)–(15), divided by $`2MH>0`$, give

```math
-2(1-b_H)-2E-D_H\le B_H.
\qquad\text{(16)}
```

This is `PairedAffine.Norm.paired_selected_normalized_bound`. There are four clearing costs, two good estimates, and two coarse estimates. The coefficient two is the ratio four divided by two, not an assertion that this is a quadratic field.

## 5. Analytic estimates and the fixed multiplier cost

At a good embedding put $`\omega_\sigma=\sigma(u)(x-\sigma(v))`$. Then
$`e^{\omega_\sigma}=z_\sigma`$, $`100|\omega_\sigma|\le\rho`$, and

```math
|j(r_{\sigma i}-\omega_\sigma)|
\le\exp(\log(2K)+\nu+\log2-\nu w_i).
\qquad\text{(17)}
```

Indeed $`r_{\sigma i}-\omega_\sigma=\sigma(u)(p_i/q_i-x)`$; use (4), $`|\sigma(u)|\le2`$, and $`\log q_i\ge w_i-1`$. The extra $`\log2`$ is not discarded.

The analytic input `Logarithm.ScaledCollision.formal_scaled_collision_bound` in `Logarithm/ScaledCollision.lean` bounds the determinant of translated period-coefficient rows. For rows assigned transverse indices with multiplicities $`n_\alpha`$, row centers $`j\omega`$, derivative orders $`\ell_r`$, and columns of weighted degree at most $`H`$, its hypotheses are $`\rho\ge100`$, $`100|\omega|\le\rho`$, $`K,H,w_0,w_*>0`$, $`w_i\ge w_*`$, $`j<K`$, and $`\sum_r\ell_r\le MH/v_0`$. Its bound is

```math
\exp\left(-c\sum_\alpha n_\alpha^2+MH(J+r_{\rm coll}(H))\right).
\qquad\text{(18)}
```

The factor $`e^{j\omega h}`$ is included. The proof invokes holomorphic collision estimates on a disk of radius $`\rho K`$; its growth cost is exactly $`J`$ from (7).

Expanding each row of (9) around $`\omega_\sigma`$ gives a finite determinant sum. The translation scalar bound contributes $`-\nu`$ times the increase in total transverse weight, plus $`MH(T+\log2/w_*)`$. Nonzero scalars have nondecreasing transverse weight. If the increase is large, the approximation saving dominates. Otherwise sufficiently many assigned indices have weight at most $`AH`$; Cauchy–Schwarz applied to their multiplicities in (18) supplies the collision saving. The capacity is
$`N_H=\#\{\alpha\in\mathbb N^m:\sum_iw_i\alpha_i\le AH\}`$, and the normalized collision rate is

```math
C_H=c\eta^2M/(HN_H)\longrightarrow C_\infty.
```

These two alternatives are combined by the maximum in the resulting bound (`PairedAffine.Analytic.minor_analytic_bound`):

```math
\frac{\log|\Delta_\sigma|}{MH}
\le V+\frac{\log2}{w_*}+r_a(H)
 +\max\{-C_H,-\nu(A(1-\eta)-b_H)\}.
\qquad\text{(19)}
```

More explicitly, consider one nonzero term of the row expansion and write $`W=\sum_r|\alpha_r|_w`$ for the total assigned transverse weight. The original total is $`MHb_H`$. If $`W\ge A(1-\eta)MH`$, the translation scalar gives at least the saving $`\nu(A(1-\eta)-b_H)MH`$; the nonpositive collision term may be omitted. If $`W<A(1-\eta)MH`$, fewer than $`(1-\eta)M`$ assigned indices can have weight greater than $`AH`$. Consequently at least $`\eta M`$ assignments belong to the set of $`N_H`$ low indices. Writing their multiplicities as $`n_\alpha`$, the inequality $`(\sum n_\alpha)^2\le N_H\sum n_\alpha^2`$ gives $`\sum n_\alpha^2\ge\eta^2M^2/N_H`$. Equation (18) supplies saving $`MHC_H`$. In this second case the translation saving may be omitted because $`W\ge MHb_H`$ for every nonzero scalar. Zero terms already satisfy either exponential upper bound. This proves the required termwise alternative, rather than requiring that every term satisfy both savings.

The expansion is an identity of finite sums, so no interchange of an infinite determinant expansion and a limit is used. The polynomial count of choices per row produces an exponential bound with exponent $`M\log(\text{row-choice count})`$. Dividing by $`MH`$ explains the remainder in (19), independent of the embedding or the chosen columns. Likewise the determinant permutation count in the coarse estimate contributes $`\log(M!)/(MH)\le\log M/H`$, explaining (20) below. The source's counting limits hold for fixed positive weights; no uniformity as dimension or approximation denominators vary is used.

The remainder $`r_a\to0`$ includes the collision remainder and the logarithm, divided by $`H`$, of the row-choice bound
$`(\lfloor H\rfloor+1)^{2m}(\lfloor H/v_0\rfloor+1)`$. The convergence references are `AlgebraicLog.LiteralAnalytic.tendsto_analyticRemainder` and `AlgebraicLog.DeterminantContradiction.tendsto_collisionRate`; their parameters are fixed. The row and low-index counts have the weighted-simplex asymptotics underlying the displayed collision limit.

At every other embedding, $`|r_{\sigma i}|\le R`$: the approximation error is at most one and (3) applies. An entrywise coefficient estimate and the determinant permutation expansion give

```math
\frac{\log|\Delta_\sigma|}{MH}\le U(R)+r_c(H),\qquad
r_c(H)=\log M/H\longrightarrow0.
\qquad\text{(20)}
```

This is `PairedAffine.AnalyticCoarse.minor_log_bound`; its only additional hypotheses are $`\log\max(1,|z_\sigma|)\le\kappa`$, nonnegative budgets, and nonzero determinant. Finally

```math
U(R)+\log2/w_*\le U(2R+2)=U(R')
\qquad\text{(21)}
```

because $`K\ge1,R\ge0`$ and
$`2\cdot2(KR+2)\le2(K(2R+2)+2)`$.
Thus the multiplier in (17) is explicitly paid by the enlarged coarse budget chosen before parameter construction.

## 6. The contradiction, with both branches

Let $`W_H=V+r_a(H)+\max\{-C_H,-\nu(A(1-\eta)-b_H)\}`$. Substitute (19)–(20) in (16) and use (21). This yields

```math
-2(1-b_H)-2E-U(R')-r_c(H)\le W_H.
\qquad\text{(22)}
```

By (8) and convergence, for every sufficiently large $`H`$, writing
$`S_H=2E+U(R')+V+r_a(H)+r_c(H)`$, one has
$`S_H<g`$ and $`2+S_H<C_H`$.

If the maximum in $`W_H`$ is its approximation term, (22) forces

```math
\nu(A(1-\eta)-b_H)-2(1-b_H)\le S_H<g.
```

But the left side equals $`g+(\nu-2)(\theta-b_H)\ge g`$, a contradiction. If the maximum is its collision term, (22) forces
$`C_H\le2(1-b_H)+S_H\le2+S_H`$, again a contradiction. Equality between the two terms causes no problem; either argument applies. These are the branches of `AlgebraicLog.quadratic_determinant_bounds_inconsistent`.

We have ruled out full row rank at all sufficiently large heights. Section 3 supplies it at a cofinal set of heights, contradiction. Therefore (4) cannot have unbounded denominators. For each $`\nu>4`$, its negation gives a threshold above which every error is strictly greater than $`q^{-\nu}`$; enlarging the threshold to at least two and weakening the strict inequality gives (1). This logical step is `AlgebraicLog.eventualLowerBoundFour_of_not_unbounded`.

## 7. The three instantiations and the exponent convention

Use $`F=\mathbb Q(\sqrt3)(\sqrt2)`$, constructed in `PairedAffine/Field.lean`. It has degree four: if $`(r+s\sqrt3)^2=2`$ with rational $`r,s`$, then $`rs=0`$; the two cases would make either two or six a rational square. Both are impossible. The generators are algebraic integers, and the four embeddings independently send them to the two signs of their positive real square roots. Write $`\sigma_{\varepsilon,\tau}(\sqrt2)=\varepsilon\sqrt2`$, $`\sigma_{\varepsilon,\tau}(\sqrt3)=\tau\sqrt3`$.

For $`x_1`$, choose $`a=2,u=1,v=\sqrt2`$, distinguished embedding $`\sigma_{+,+}`$, and good embeddings $`\sigma_{+,+},\sigma_{+,-}`$. Both have $`u(x_1-v)=\log2`$, so (2) holds, with scale one and distinguished base two. For $`x_2`$, choose $`a=4,u=\sqrt2,v=0`$ and the same good embeddings. Their affine exponent is $`\sqrt2(\sqrt2\log2)=2\log2`$, whose exponential is four; the scale is $`\sqrt2\le2`$. These are the two constructions in `PairedAffine/AffineExamples.lean`. The auxiliary square root of three makes two distinct good embeddings even though the defining data lie in a smaller field.

For $`x_3`$, choose $`a=3+2\sqrt2,u=\sqrt2,v=\sqrt3`$, distinguished embedding $`\sigma_{+,+}`$, and good embeddings $`\sigma_{+,+},\sigma_{-,+}`$. Put $`b_0=3+2\sqrt2>1`$. At these embeddings the affine exponent is respectively $`\log b_0`$ and $`-\log b_0`$. Since
$`(3+2\sqrt2)(3-2\sqrt2)=1`$, their exponentials are precisely the corresponding images of $`a`$. Both scales are $`\sqrt2\le2`$. All three targets are positive, and all selected elements are integral. The identities are `PairedAffine.Concrete.compatible`, `PairedAffine.Concrete.scale_norm_le`, and `PairedAffine.shifted_period_eventualLowerBound` in `PairedAffine/Concrete.lean` and `PairedAffine/Main.lean`.

For completeness, (1) implies irrationality without a separate transcendence input. If $`x=r/s`$ were rational, take an arbitrarily large multiple $`q=Ns`$, $`p=Nr`$. Its error is zero, contradicting the positive lower bound at, for example, $`\nu=5`$.

The standard exponent in `OAI/NumberTheory/PiExponent/Statement.lean` is the supremum of positive real $`\nu`$ for which infinitely many distinct reduced rationals $`r`$, of denominator at least two, satisfy $`0<|x-r|<\mathrm{den}(r)^{-\nu}`$. For every $`\nu>4`$, (1) forces the denominator of such a rational below $`Q`$. Its error is less than one, so its numerator also lies in a bounded interval for each of these finitely many denominators. There are therefore only finitely many such rationals. For irrational $`x`$, the approximation-exponent set is nonempty (the inherited Dirichlet consequence `two_mem_approximationExponents` supplies exponent two), and all its members are at most four. Its supremum is at most four. The corresponding deductions are `AlgebraicLog.irrational_of_eventualLowerBoundFour` and `irrationalityExponent_le_four_of_eventualLowerBoundFour` in `AlgebraicLog/ExponentConsequence.lean`, applied separately to the three bounds above.
