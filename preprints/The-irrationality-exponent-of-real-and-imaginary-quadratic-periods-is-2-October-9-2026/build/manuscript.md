# The irrationality exponent of real and imaginary quadratic periods is 2

Ryan Matthew Casper · October 9, 2026

## Abstract

We prove that $\pi/\sqrt r$ has irrationality exponent two for every positive rational $r$. We also prove that this exponent is two for $\log\alpha/\sqrt d$, where $d>1$ is a squarefree integer and $\alpha\ne1$ is a positive norm-one element of $\mathbb Q(\sqrt d)$, and for every nonzero real $x$ satisfying $\exp(i\sqrt d\,x)\in\mathbb Q(i\sqrt d)$, where $d$ is a positive integer. The imaginary quadratic result includes every real branch, including those whose exponential is a root of unity. The arguments build on OpenAI's weighted logarithmic interpolation and determinant method, together with our extension to distinct multiplicative centres. We apply these methods in quadratic orders. In the real quadratic case, one cleared determinant is evaluated at both embeddings; a norm lower bound is compared with the average of two analytic upper bounds. The periodic case uses the positive norm in an imaginary quadratic order and supplies the torsion cases of the imaginary quadratic theorem. All approximation bounds are eventual and noneffective. A Lean formalization accompanies the proof.

## 1. Introduction and main results

For an irrational real number $x$, write
$$
\mu(x)=\sup\left\{\nu>0:
0<\left|x-\frac pq\right|<q^{-\nu}
\text{ for infinitely many reduced fractions }p/q,\ q\ge2\right\}.
$$
The supremum is understood in the extended real line. Dirichlet's theorem gives $\mu(x)\ge2$. For the families considered here, we prove that every exponent greater than two eventually fails. More precisely, we establish the property
$$
\begin{split}
\mathcal E(x):\quad &\forall\nu\in\mathbb R,\ \nu>2\ \Longrightarrow\\
&\exists Q\in\mathbb N,\ Q\ge2,\quad
\forall p\in\mathbb Z\ \forall q\in\mathbb N,\ q\ge Q\ \Longrightarrow\\
&\hspace{35mm}q^{-\nu}\le\left|x-\frac pq\right|.
\end{split}                                                    \tag{1}
$$
Fractions in (1) need not be reduced. The threshold may depend on $x$ and $\nu$, and is uniform in $p,q$.

**Theorem 1.** Property $\mathcal E(x)$ holds in each of the following cases, and consequently $x$ is irrational and $\mu(x)=2$.

1. $r\in\mathbb Q$, $r>0$, and $x=\pi/\sqrt r$.
2. $d\in\mathbb N$ is squarefree, $d>1$, and $A,B\in\mathbb Q$ satisfy
   $$A^2-dB^2=1,\qquad \alpha=A+B\sqrt d>0,\qquad\alpha\ne1;$$
   then $x=\log\alpha/\sqrt d$.
3. $d\in\mathbb N$, $d>0$, $x\in\mathbb R\setminus\{0\}$, and $A,B\in\mathbb Q$ satisfy
   $$\exp(i\sqrt d\,x)=A+Bi\sqrt d.$$

Part 2 allows rational coefficients and values $\alpha$ below one. Part 3 holds for every positive integer $d$ and every real branch of the exponential identity, including roots of unity. It combines the periodic and non-torsion imaginary cases and contains part 1: if $r=a/b>0$, take $d=4ab$ to obtain $\sqrt d\,\pi/\sqrt r=2b\pi$. We state part 1 separately because its periodic argument supplies the torsion cases of part 3.

The normalization by $\sqrt d$ is essential to this argument; it does not establish exponent two for the corresponding unnormalized logarithms. For unnormalized logarithms of arbitrary positive degree-two algebraic numbers, [Q4] proves a general upper bound of four. The thresholds are not made effective or uniform as the field varies. The result gives neither a positive constant in a $q^{-2}$ lower bound nor bounded continued-fraction partial quotients.

The common argument compares two estimates for one interpolation determinant. Geometry produces a nonzero minor with the prescribed polynomial degree. Arithmetic gives a lower bound with leading cost one. The analytic upper bound has two cases: repeated low transverse indices give a collision saving, while high indices contribute powers of the small approximation errors. In the quadratic case, compatible exponentials at both embeddings allow the two estimates to be compared without increasing the leading arithmetic cost. The periodic case treats coincident multiplicative centres.

We use the geometric and analytic results of OpenAI's manuscript and released library [O], together with the extension to distinct multiplicative centres in [R]. Sections 2 and 5 state the inherited results and explain their application. We prove the quadratic and rational-radicand extensions, combine the torsion and non-torsion cases, and give their formalization.

## 2. Weighted logarithmic interpolation

Throughout, logarithms are natural. All multi-indices have nonnegative integer entries; $w\cdot a=\sum_iw_i a_i$. Geometry and formal coefficients are over $\mathbb C$.

### 2.1 Numerical hypotheses and prescribed packets

Fix $m,K\ge1$, positive rational weights
$$
W=(w_0,w_1,\ldots,w_m),\qquad
V=(v_0,w_1/\theta,\ldots,w_m/\theta),\qquad 0<\theta<1,
$$
and a positive rational $\sigma$. Put
$$
\mathcal C(m,\sigma)=2(m+2)^{m+2}
       \left(1+\frac{m+2}{\sigma}\right)^{m+2}.
$$
Require
$$
K(1+3\sigma)^{m+1}\frac{\prod_{a=0}^mW_a}{\prod_{a=0}^mV_a}<1,
\qquad (1+\sigma)\theta<1.                         \tag{2}
$$
There is also a separated-product hypothesis. For equal-cardinality subsets $I,J\subseteq\{0,\ldots,m\}$, whenever the largest index in their symmetric difference is positive and belongs to $I$, require
$$
\mathcal C(m,\sigma)\prod_{a\in J}V_a
       <\prod_{a\in I}W_a.                         \tag{3}
$$
This is `PersistentWeightComparison.comparisonConstant` in [O]. It depends on $m,\sigma$ and is independent of the centres.

At centres $(y_j,c_{j1},\ldots,c_{jm})$, $0\le j<K$, consider the formal expansions
$$
P\bigl(y_j(1+t),c_{j1}+\log(1+t)+u_1,\ldots,
                  c_{jm}+\log(1+t)+u_m\bigr).       \tag{4}
$$
The target packet consists of all coefficients $[t^su^b]$ with
$$v_0s+(w\cdot b)/\theta<H.$$
There are two interpolation cases.

**Distinct multiplicative centres.** The numbers $y_j$ are nonzero and pairwise distinct; the $c_{ji}$ are arbitrary complex numbers. Hypotheses (2)--(3) suffice.

**Periodic centres.** All $y_j=1$, every map $j\mapsto c_{ji}$ is injective, and, in addition to (2)--(3),
$$K(1+3\sigma)^m\theta^m<1.                       \tag{5}$$
The periodic case requires the fibre-volume condition (5) as well as the total-volume condition (2).

**Interpolation theorem.** In either case there is a positive rational scale $R$, depending on the weights, such that for all sufficiently large integers $n$, every collection of these packets at height $H=nR$ is realized by a polynomial supported on
$$w_0h+w\cdot\gamma\le H.                         \tag{6}$$
The eventual threshold may depend on the fixed centres, but the weight conditions are independent of them. We can therefore select the weights from successive approximation denominators before forming the centres. The polynomial support in (6) and the packet cutoff use the same height $H=nR$. This equality of degree scales is needed in the determinant estimates below.

For the first case the source theorem is `Logarithm.eventually_weighted_logarithmic_interpolation` in [R]. For the second it is `PeriodicInterpolation.eventual_packets` in the accompanying `PeriodicGeometry/Interpolation.lean`, using the periodic curve theorem from [O]. Namespace prefix `OAI` is omitted in source anchors in this paper.

### 2.2 Curve contact, ampleness, and sections

We recall the geometric argument for the interpolation theorem. For an integral curve in the affine coordinates $(Y,X_1,\ldots,X_m)$, take its smooth complete model and set
$$
\deg_W C=\sum_P\max\left\{0,
 -\frac{\operatorname{ord}_P Y}{w_0},
 -\frac{\operatorname{ord}_P X_1}{w_1},\ldots,
 -\frac{\operatorname{ord}_P X_m}{w_m}\right\}.      \tag{7}
$$
An identically zero coordinate contributes no pole. At a branch through the $j$th centre, put $t=Y/y_j-1$ and
$$
h_P=\min\left\{
\frac{\operatorname{ord}_P t}{V_0},
\frac{\operatorname{ord}_P(X_i-c_{ji}-\log(1+t))}{V_i}:1\le i\le m
\right\}.                                       \tag{8}
$$
The logarithm is a formal series; infinite orders are allowed in the minimum. The curve is nonconstant, so at least one order is finite. The inherited curve inequality is
$$ (1+\sigma)\sum_{P\text{ over centres}}h_P\le\deg_W C.       \tag{9}$$
The function field is an essentially finite type extension $E/\mathbb C$ of transcendence degree one, generated by the coordinate functions. For positive $W,V$ satisfying (2)--(3) and the stated centre hypotheses, the curve theorem gives (9) for all branches, with the weights in (7)--(8). The periodic case also requires (5). This is the curve-inequality proposition in [O, §2]; the distinct-centre version is `Logarithm.weighted_curve_inequality`, and the periodic application is `PeriodicGeometryData.exact_weighted_curve_inequality`.

Choose $R$ so that $R/W_a$ and $R/V_a$ are positive integers and the monomials of $W$-degree at most $R$ contain every coordinate. The projective closure $X$ of this monomial embedding is integral, projective and Noetherian. Its constant-coordinate chart is the original affine space, and $L=\mathcal O_X(1)$ is ample. On a curve meeting this chart,
$$\deg(L|_C)=R\deg_W C.                           \tag{10}$$
Pure coordinate powers attain the largest pole in (7), which gives the equality in (10).

Choose Taylor polynomials $G_i^{\rm geom}$ for which the first omitted $t$-power has $V$-weight strictly greater than $V_i$. At each centre use local coordinates
$$t=Y/y_j-1,\qquad u_i'=X_i-c_{ji}-G_i^{\rm geom}(t),$$
and the finite-colength ideal
$$I_j=(t^{R/V_0},(u_1')^{R/V_1},\ldots,(u_m')^{R/V_m}).$$
The distinct full centres give a coherent ideal sheaf $I$ on $X$, with these local ideals and the unit ideal away from the centres. Taylor truncation preserves (8). On a branch, $\operatorname{ord}_P I=Rh_P$.

Let $p:X'\to X$ be the ordinary blowup of $I$ and write $I\mathcal O_{X'}=\mathcal O_{X'}(-E)$. Put $\mathcal A=p^*L$. For a noncontracted curve meeting the affine chart, the degree identities are
$$
\deg(\mathcal A|_C)=R\deg_W p(C),\qquad
\deg(\mathcal O(-E)|_C)=-R\sum_Ph_P.               \tag{11}
$$
These identities follow by passing to the curve's function field and normalization. This construction, given by `PeriodicCurveModel.degreeData` in the periodic extension, supplies the curve data to which (9) applies.

Equation (9) makes $\mathcal A-(1+\sigma)E$ nef. Curves contracted by $p$ are covered by relative ampleness of $-E$; curves outside the affine chart avoid the exceptional support. For some integer $a>1$, $a\mathcal A-E$ is ample. The identity
$$
\mathcal A-E=
\frac{a-1}{a(1+\sigma)-1}\bigl(\mathcal A-(1+\sigma)E\bigr)
+\frac{\sigma}{a(1+\sigma)-1}(a\mathcal A-E)         \tag{12}
$$
then makes $\mathcal A-E$ ample. The auxiliary integer $a$ is used only to prove ampleness; the final polynomial bound remains $nR$.

We now apply the section theorem. For a proper scheme $X$ over a Noetherian ring, an ideal sheaf $I$, and a line bundle $L$, ampleness of $p^*L\otimes\mathcal O(-E)$ on the ordinary blowup implies that, for all sufficiently large $n$,
$$
H^0(X,L^n)\longrightarrow H^0(X,L^n\otimes\mathcal O_X/I^n)
\quad\hbox{is surjective}.                        \tag{13}
$$
The proof uses eventual recovery of the ordinary Rees algebra's graded pieces and Serre vanishing. The quotient in (13) uses ordinary ideal powers $I^n$, and the conclusion is required only for sufficiently large $n$. The Lean declaration is `BlowupJetSurjectivity.eventual_blowup_jetRestriction_surjective` in [O]. The projective monomial construction over $\mathbb C$ supplies the base, properness, and coherence hypotheses.

Full-centre localization and the Chinese remainder theorem identify the quotient data with the local finite-colength quotients. Each generator of $I_j$ has weight $R$, so $I_j^n$ has weighted order at least $nR$. Surjectivity in (13) therefore supplies every packet of weight *strictly less* than $nR$. Equality between an ideal power and the weighted-order ideal is not required. The geometric Taylor-coordinate change and its inverse preserve the packet filtration.

Finally, for sufficiently large $n$, sections of $L^n$ are restrictions of homogeneous degree-$n$ polynomials in the monomial embedding coordinates. In the constant-coordinate trivialization their affine polynomials have $W$-support at most $nR$. This is `WeightedGlobalSectionBound.eventual_supportBound`. Intersecting this eventual range with that of (13) gives the interpolation theorem at the same $n$. The periodic argument is completed in `PeriodicJetPackets.formalPackets_surjective_of_jetRestriction`; the distinct-centre argument is in `Logarithm/GeometricInterpolation.lean`.

## 3. Parameter selection

We first prove $\mathcal E(x)$ for two kinds of data. In the **paired quadratic case**, let $D\in\mathbb Z$ be nonsquare, let $\beta^2=D$ in $\mathbb C$, and put $\beta_+=\beta$, $\beta_-=-\beta$. Let
$$\mathcal O=\mathbb Z[\sqrt D],\qquad a\in\mathcal O,\qquad c\in\mathbb N_{>0},$$
with embeddings $\sigma_\pm(\sqrt D)=\beta_\pm$. Assume $x\ne0$ and
$$
e^{\beta_\pm x}=\sigma_\pm(a)/c=:z_\pm,
\qquad n\longmapsto z_\pm^n\text{ is injective on }\mathbb N.   \tag{14}
$$
In the **periodic case**, take an integer $d>0$, $\beta=i\sqrt d$, $x\ne0$, and
$$e^{\beta x}=1.                                  \tag{15}$$
Here the order is $\mathbb Z[\sqrt{-d}]$, and $a=c=1$. The integer $d$ need not be squarefree. We will derive the approximation bound from these algebraic and exponential conditions.

Choose $M\ge1$ with $|\beta|\le M$ (and thus $|\beta_-|\le M$), and put
$$
\lambda=\log M,\qquad \rho=100\max(1,M|x|),\qquad
\delta=\log c,\qquad \kappa=\frac{\log2}{4}.
$$
In the periodic case $c=1$, so $\delta=0$. The radius satisfies $\rho\ge100$ and $\rho\ge100|\beta_\pm x|$. Let $C_{\rm lcm}=4+\log4$, an inherited admissible constant for
$$\log\operatorname{lcm}(1,\ldots,T)\le C_{\rm lcm}T,$$
and reserve $\Lambda=C_{\rm lcm}+\lambda$ in the numerical construction.

Fix $\nu>2$. If (1) fails, there are arbitrarily large $q$ with
$$\left|x-\frac pq\right|\le q^{-\nu}.             \tag{16}$$
The use of a weak upper inequality only enlarges the hypothetical set. Because $x\ne0$, sufficiently large such denominators have $p\ne0$.

Choose rational numbers $\theta,A_0,B_0,C_0$ and a real $\eta$ with
$$
0<\theta<A_0<B_0<1,\quad C_0>1,\quad
C_0B_0<1,\quad B_0<C_0\theta<1,\quad 0<\eta<1,
$$
such that
$$g=\nu\bigl(A_0(1-\eta)-\theta\bigr)-(1-\theta)>0.           \tag{17}$$
These parameters are supplied by the inherited `exists_parameters` construction, applied at the given exponent $\nu$.

Take $0<\varepsilon<g$ with $\varepsilon\le1/2$, then $F>2/\theta$ so that $\nu/F<\varepsilon/3$. Set
$$
K=\lfloor C_0^m\rfloor,\qquad w_0=B_0^{-m},\qquad
v_0=2K\theta^mw_0.                                \tag{18}
$$
Then $K(w_0/v_0)\theta^m=1/2$ and $K\theta^m<1$. As $m$ increases, $K/w_0$ and $m/v_0$ tend to zero, whereas
$$
\kappa\frac{\eta^2K\theta^m}{(m+1)v_0A_0^m}
=\frac{\kappa\eta^2}{2(m+1)}(B_0/A_0)^m
\longrightarrow\infty.                            \tag{19}
$$
Choose one finite $m\ge1$ so that the expression in (19) exceeds two and
$$
\frac{\Lambda Fm+2\log2}{v_0}
+\frac{(\rho+\delta)K}{w_0}<\varepsilon/3.          \tag{20}
$$
Choose a small positive rational $\sigma$ satisfying (2) and (5). The latter is harmless in the paired case and necessary in the periodic case.

Now select $m$ approximants $r_i=p_i/q_i$ from (16), with $q_i\ge2$ and $p_i\ne0$, successively far enough out that
$$w_i=\lceil\log q_i\rceil$$
satisfy (3). This successive choice works because, after common factors are cancelled in a separated-product inequality, its largest differing weight lies on the side to be made large; all other uncancelled weights have smaller indices. Ratios from higher common indices equal $\theta$ and are already fixed. There are only finitely many conditions at each step, none depending on the as yet unchosen centres.

Let $w_* =\min_iw_i>0$. Also impose
$$
\Lambda\sum_i\frac1{w_i}
+\frac{\theta+\log4+\log(2K)+\nu+\log(2\rho K)}{w_*}
<\varepsilon/3.                                  \tag{21}
$$
All numerators in this requirement were fixed before the approximation denominators. Arbitrarily large denominators make it possible. Finally put
$$
T_i=\left\lceil\frac{Fw_i}{v_0}\right\rceil,
\qquad G_i(t)=\sum_{1\le k<T_i}\frac{(-1)^{k+1}t^k}{k}.        \tag{22}
$$
Thus $T_iv_0\ge Fw_i>w_i/\theta$. The formal change from $\log(1+t)$ to $G_i$ preserves interpolation surjectivity for the packets in §2; it need not preserve each coefficient individually. This is the truncated-interpolation theorem in [R].

For later comparison, define
$$
\begin{aligned}
E_{\rm ar}&=\frac{\Lambda Fm}{v_0}
 +\Lambda\sum_i\frac1{w_i}+\frac\theta{w_*}+\frac{K\delta}{w_0},\\
E_{\rm tr}&=\frac\nu F+\frac{\log2}{v_0}
 +\frac{\log4+\log(2K)+\nu}{w_*},\\
E_{\rm hol}&=\frac{\rho K}{w_0}+\frac{\log2}{v_0}
 +\frac{\log(2\rho K)}{w_*},\qquad
E_{\rm an}=E_{\rm tr}+E_{\rm hol}.
\end{aligned}                                                    \tag{23}
$$
Equations (20)--(21) give $E:=E_{\rm ar}+E_{\rm an}<\varepsilon<g$. With
$$c_\infty=\frac{\kappa\eta^2K\theta^m}{(m+1)v_0A_0^m},$$
we also have $c_\infty>2>1+E$. This entire construction is `Logarithm.exists_admissible_parameters`, applied with $(x,\nu,\Lambda,\kappa,\rho,\delta)$. Dimension, weights, approximants, centres and truncations are now fixed. Only $H$ will tend to infinity.

## 4. The arithmetic lower bound

For either sign in (14), put $\omega_\pm=\beta_\pm x$ and use the literal centres
$$y_j=z_\pm^j,\qquad c_{ji}=\beta_\pm j r_i.$$
The powers in (14) make the $y_j$ distinct and nonzero. For (15), take $y_j=1$ and $c_{ji}=\beta j r_i$; each $j\mapsto c_{ji}$ is injective because $\beta,p_i,q_i$ are nonzero. Thus the two cases satisfy the respective interpolation hypotheses of §2.

At each sufficiently large admissible $H=nR$, rows are $(j,s,b)$ with
$$0\le j<K,\qquad v_0s+(w\cdot b)/\theta<H,$$
and columns are $(h,\gamma)$ with $w_0h+w\cdot\gamma\le H$. The matrix entries are
$$
E^\pm_{(j,s,b),(h,\gamma)}
=[t^su^b]\ z_\pm^{jh}(1+t)^h
          \prod_i(\beta_\pm jr_i+G_i(t)+u_i)^{\gamma_i}.          \tag{24}
$$
The periodic matrix is the same formula with $z=1$. Interpolation says its linear map is surjective, hence a square minor using every row is nonzero. Write $N_H$ for the row count and select such a minor once. In the paired case, choose it at $\sigma_+$; the determinant at $\sigma_-$ always uses the same selected columns. Put
$$b_H=\frac{\sum_{\rm rows}w\cdot b}{N_HH},\qquad 0\le b_H\le\theta. \tag{25}$$
For $H>0$ there is at least one row, so the normalization is positive.

Let $L_i=\operatorname{lcm}(1,\ldots,T_i)$ and
$$D_H=\prod_iL_i^{\lfloor H/w_i\rfloor}.$$
For each row and selected column multiply (24) by
$$D_H\left(\prod_iq_i^{-b_i}\right)
          \left(c^{Kh}\prod_iq_i^{\gamma_i}\right).             \tag{26}$$
If $b\not\le\gamma$ the entry is zero. Otherwise the result is the embedding of the following element of $\mathcal O$:
$$
D_H\,a^{jh}c^{(K-j)h}\binom\gamma b
[t^s](1+t)^h\prod_i(jp_i\sqrt D+q_iG_i(t))^{\gamma_i-b_i}.      \tag{27}
$$
Here $j<K$ makes $(K-j)h$ nonnegative. Every $L_iG_i$ has integer coefficients, and $\gamma_i-b_i\le\lfloor H/w_i\rfloor$; hence (27) is integral in the stated order. In the periodic case $a=c=1$ and $D=-d$.

This constructs one order-valued matrix $B_H$, independent of the embedding. If $\Delta_H^\pm$ denote the selected determinants, then
$$
\sigma_\pm(\det B_H)=C_H\Delta_H^\pm,\qquad
C_H=D_H^{N_H}
 \prod_{\rm columns}\left(c^{Kh}\prod_iq_i^{\gamma_i}\right)
 \prod_{\rm rows}\prod_iq_i^{-b_i}>0.               \tag{28}
$$
The entries in (27) are integral, although the common factor $C_H$ may be rational. The inverse row factors in (28) will reduce the denominator cost in the lower bound.

Nonvanishing at one embedding gives $\det B_H\ne0$. In the paired case the order norm is a nonzero integer, so
$$1\le|\sigma_+(\det B_H)|\,|\sigma_-(\det B_H)|.$$
Both determinants are nonzero, and, on putting
$$\mathcal L_H=\frac{\log|\Delta_H^+|+\log|\Delta_H^-|}{2N_HH},$$
we obtain $\mathcal L_H\ge-\log C_H/(N_HH)$. The norm controls the product of the two embedded determinants, and hence the average of their logarithms.

In the periodic case a nonzero element $u+v\sqrt{-d}$ has
$$|u+vi\sqrt d|^2=u^2+dv^2\in\mathbb Z_{>0}.$$
Thus $|\sigma(\det B_H)|\ge1$, and the same lower bound holds with $\mathcal L_H=\log|\Delta_H|/(N_HH)$. This norm argument applies to every positive integer $d$ and does not require a maximal order.

We next estimate the clearing cost. From $T_i\le Fw_i/v_0+1$,
$$\frac{\log D_H}{H}\le\frac{C_{\rm lcm}Fm}{v_0}
                       +C_{\rm lcm}\sum_i\frac1{w_i}.$$
A column costs at most $H+HK\delta/w_0$, because $\log q_i\le w_i$ and $h\le H/w_0$. A row saves
$$
\sum_i b_i\log q_i\ge w\cdot b-\sum_i b_i
                         \ge w\cdot b-\theta H/w_*.
$$
Therefore
$$
\mathcal L_H\ge-(1-b_H)-E_{\rm ar}^{\rm raw},\qquad
E_{\rm ar}^{\rm raw}=
\frac{C_{\rm lcm}Fm}{v_0}+C_{\rm lcm}\sum_i\frac1{w_i}
+\frac\theta{w_*}+\frac{K\delta}{w_0}.             \tag{29}
$$
Since the minimum weight is attained and $\lambda\ge0$,
$$\lambda/w_*\le\lambda\sum_i1/w_i,\qquad \lambda Fm/v_0\ge0.$$
Using the reserve $\Lambda=C_{\rm lcm}+\lambda$, we obtain the weaker bound
$$\mathcal L_H\ge-(1-b_H)-(E_{\rm ar}-\lambda/w_*).             \tag{30}$$
The identities for the two embeddings are formalized in `Quadratic/ScaledArithmetic.lean` as `map_clearedMinor`, `map_clearedMinor_flip`, and `selectedMinor_clearing_bound`. Inequality (30) is `DeterminantData.actual_minor_arithmetic_lower_bound`. The periodic modules give the corresponding single-embedding estimate.

## 5. The analytic upper bound

We estimate the same minor by applying the translation and collision theorems. Fix a sign and write $\beta,\omega,z$ for that sign's data. Both signs use the same radius and weights.

For a transverse index $a$ and a column $(h,\gamma)$ define the entire function
$$
f_{a,h,\gamma}(Z)=[u^a]e^{hZ}\prod_i(Z+u_i)^{\gamma_i}.
$$
It is zero unless $a\le\gamma$; otherwise it is
$\binom\gamma a e^{hZ}Z^{|\gamma|-|a|}$. At row centre $j$, substitute
$$Z_j(t)=j\omega+\log(1+t),\qquad e^{Z_j(t)}=z^j(1+t).$$
The additive coordinates in (24) become
$$Z_j(t)+u_i+e_{ji}+\tau_i(t),\quad
e_{ji}=\beta j(r_i-x),\quad \tau_i=G_i-\log(1+t).$$
Expanding in the errors and tails expresses each row as a finite sum of tests of the $f_{a,h,\gamma}$. Multilinearity gives the corresponding expansion of the selected determinant, with the column selection fixed throughout.

### 5.1 Translation coefficients

The coefficient multiplying each row test is independent of the column. A row choice includes $a$ with $w\cdot a\le H$, a distribution of error and tail factors, and a coefficient order $k\le s$. A nonzero coefficient requires $a\ge b$ coordinatewise. From (16) and $w_i-1\le\log q_i$,
$$|e_{ji}|\le\exp\bigl(\log(2K)+\nu+\lambda-\nu w_i\bigr).$$
The tails start at order $T_i$, and $Fw_i\le v_0T_i$. Applying the inherited row-scalar estimate with error constant $\log(2K)+\nu+\lambda$, derivative order $k\le s<H/v_0$, and lower weight $w_*$ gives
$$
|\text{row scalar}|\le
\exp\left\{-\nu(w\cdot a-w\cdot b)
          +H(E_{\rm tr}+\lambda/w_*)\right\}.      \tag{31}
$$
This is `MatrixTranslationBounds.norm_rowScalar_exp_weight_difference`, applied to the quadratic data in `LiteralAnalytic.norm_choiceScalar_le`. The exponent in the estimate is the original approximation exponent $\nu$.

### 5.2 Collision estimate

Group rows by their chosen transverse index $a$, and let $n_a$ be the group sizes. For row tests of order $\ell=s-k$, the inherited complex-period collision theorem gives
$$
|\det(\text{row tests})|\le
\exp\left\{-\kappa\sum_a n_a^2
              +N_HH(E_{\rm hol}+r_H)\right\}.      \tag{32}
$$
We apply the theorem with period $\omega=\beta x$, radius $\rho\ge\max(100,100|\omega|)$, row labels $0\le j<K$, column exponents satisfying (6), weights $w_i\ge w_*>0$, and
$$\sum_{\rm rows}\ell\le N_HH/v_0.$$
The theorem retains the factor $e^{j\omega h}=z^{jh}$ and uses the given period $\omega$, without restriction to a principal logarithm. It gives the collision constant $\kappa=\log2/4$ and the holomorphic error in (23), where $\log(200K)+\log(\rho/100)=\log(2\rho K)$.

The complex-period extension of the collision lemma in [O, §3] gives (32). Its proof expands the entire functions in Taylor series. Rows with the same transverse index test the same family of functions, so repeated Taylor degrees within a group annihilate determinant terms. The remaining distinct degrees give the quadratic saving in $n_a$. The remainder $r_H$ is `Collision.collisionRemainder N_H H`; it tends to zero by the row-count asymptotic below. The estimate is formalized in `Logarithm.ScaledCollision.formal_scaled_collision_bound`.

### 5.3 The determinant estimate and its limits

Set
$$N_{A_0}(H)=\#\{a\in\mathbb N^m:w\cdot a\le A_0H\},\qquad
c_H=\frac{\kappa\eta^2N_H}{H N_{A_0}(H)}.$$
If at least $\eta N_H$ rows have $w\cdot a\le A_0H$, Cauchy--Schwarz gives
$$\sum_a n_a^2\ge\eta^2N_H^2/N_{A_0}(H).$$
Otherwise $\sum_{\rm rows}w\cdot a\ge A_0(1-\eta)N_HH$. Every nonzero scalar product also satisfies $\sum w\cdot a\ge\sum w\cdot b=N_HHb_H$. Combining (31)--(32) therefore bounds every summand by
$$
\exp\left\{N_HH\left[
E_{\rm an}+\lambda/w_*+r_H+
\max\{-c_H,-\nu(A_0(1-\eta)-b_H)\}\right]\right\}.            \tag{33}
$$
The two cases are combined in `DeterminantAnalyticBound.translated_summand_bound`.

The number of row choices is at most
$$Q_H=(\lfloor H\rfloor+1)^{2m}(\lfloor H/v_0\rfloor+1).$$
Consequently the determinant expansion has at most $Q_H^{N_H}$ summands. The logarithmic cost of summing them, after division by $N_HH$, is at most $\log Q_H/H$, which tends to zero.

For fixed positive weights, counting lattice points in the row and transverse simplices gives
$$
\begin{aligned}
N_H&\sim\frac{K\theta^m}{(m+1)!v_0\prod_iw_i}\,H^{m+1},\\
N_{A_0}(H)&\sim\frac{A_0^m}{m!\prod_iw_i}\,H^m,\\
c_H&\longrightarrow c_\infty
 =\frac{\kappa\eta^2K\theta^m}{(m+1)v_0A_0^m}.
\end{aligned}                                                    \tag{34}
$$
The leading constants are positive, and the strict row cutoff and weak transverse cutoff give the respective leading simplex volumes. The family declarations `tendsto_collisionRate` and `tendsto_analyticRemainder` apply these inherited weighted-simplex asymptotics to the row set of the interpolation matrix.

We conclude, uniformly in the selected columns,
$$
\frac{\log|\Delta_H|}{N_HH}\le
E_{\rm an}+\lambda/w_*+o(1)
+\max\{-c_H,-\nu(A_0(1-\eta)-b_H)\}.              \tag{35}
$$
In the paired case, (14) supplies the estimate at both embeddings, with the same row set, column selection, $b_H$, $c_H$, and error bounds. Averaging gives (35) with its left side replaced by $\mathcal L_H$. Estimating the same minor at both embeddings is what preserves the leading arithmetic cost one.

## 6. The determinant contradiction

Compare (30) and (35). The slope terms cancel exactly:
$$ (E_{\rm ar}-\lambda/w_*)+(E_{\rm an}+\lambda/w_*)=E.        \tag{36}$$
The arithmetic reserve also includes the nonnegative term $\lambda Fm/v_0$. The generator size therefore contributes no additional leading coefficient, and the collision constant remains $\log2/4$.

At least one of the two alternatives would have to hold:
$$c_H\le1-b_H+E+o(1),                              \tag{37}$$
or
$$\nu(A_0(1-\eta)-b_H)\le1-b_H+E+o(1).             \tag{38}$$
The first is impossible for large $H$, because $b_H\ge0$ and $c_H\to c_\infty>1+E$. For the second, (17) and $b_H\le\theta$ give
$$
\nu(A_0(1-\eta)-b_H)-(1-b_H)
=g+(\nu-1)(\theta-b_H)\ge g>E.                    \tag{39}
$$
Choose a fixed positive margin smaller than both $c_\infty-(1+E)$ and $g-E$. The asymptotic errors are eventually smaller than this margin. We then choose an admissible interpolation height $H=nR$ beyond all the resulting thresholds. The selected nonzero minor violates both alternatives, proving $\mathcal E(x)$ under (14) and under (15).

The result is formalized as `DeterminantContradiction.period_eventualLowerBound` in each family. All parameters and approximation data remain fixed as the degree tends to infinity. The proof applies the arithmetic and analytic estimates to one selected minor and intersects their eventual ranges before using cofinal matrix surjectivity.

## 7. The quadratic families

### 7.1 Positive norm-one elements

Let $d,A,B,\alpha$ satisfy Theorem 1(2). Squarefreeness and $d>1$ make $d$ nonsquare. Write $A=a/c$, $B=b/c$ with integers $a,b$ and a positive integer $c$; for example, the product of the rational denominators suffices. The norm equation becomes
$$a^2-db^2=c^2.$$
Use $D=d$, $\beta=\sqrt d$, and the order numerator $a+b\sqrt d$. Since $\alpha>0$ and its conjugate is $\alpha^{-1}>0$, the real number
$$x=\frac{\log\alpha}{\sqrt d}$$
satisfies
$$e^{\sqrt d\,x}=\alpha,\qquad e^{-\sqrt d\,x}=\alpha^{-1}.$$
The condition $\alpha\ne1$ gives $x\ne0$. Powers of either positive number $\alpha,\alpha^{-1}$ are injective: an equality of powers and injectivity of the real exponential imply equality of the exponents, since $\log\alpha\ne0$. Thus (14) applies, proving part 2 for both signs of $\log\alpha$.

### 7.2 Non-torsion imaginary elements

Let $d>0$ and suppose $e^{i\sqrt d\,x}=A+Bi\sqrt d=:z$, with no positive power of $z$ equal to one. The integer $D=-d$ is nonsquare. Express $A,B$ over a common positive integer denominator and use the numerator in $\mathbb Z[\sqrt{-d}]$. Complex conjugation of the given identity yields
$$e^{-i\sqrt d\,x}=\overline z.$$
Non-torsion implies $x\ne0$ and injectivity of both power sequences: cancel the smaller power in an equality and obtain a forbidden positive power equal to one; conjugation preserves this condition. Hence (14) proves $\mathcal E(x)$.

For every integer $k$, the value $x+2\pi k/\sqrt d$ satisfies the same exponential identity, so (14) applies to each real branch.

### 7.3 Division by a positive integer

The eventual bound is preserved by division by a positive integer. Suppose $n\in\mathbb N_{>0}$ and $\mathcal E(y)$ holds. Given $\nu>2$, choose $\mu=(\nu+2)/2$, so $2<\mu<\nu$. For all sufficiently large $q$ and every integer $p$,
$$
\left|\frac yn-\frac pq\right|
=\frac1n\left|y-\frac{np}{q}\right|
\ge\frac1nq^{-\mu}\ge q^{-\nu},
$$
where the final inequality follows eventually from $q^{\nu-\mu}\ge n$. The larger threshold depends on $n$ and $\nu$, not on $p$. The formal lemma is `Imaginary.eventualLowerBound_div_nat`.

### 7.4 Torsion and rational radicands

If $z=e^{i\sqrt d\,x}$ has $z^n=1$ for some positive integer $n$, then
$$e^{i\sqrt d\,(nx)}=1.$$
For $x\ne0$, also $nx\ne0$. Applying the periodic result to this nonzero multiple gives $\mathcal E(nx)$, and §7.3 gives $\mathcal E(x)$. Together with §7.2 this proves part 3, including $z=1$. The argument uses only the existence of a positive torsion order, so no classification of quadratic roots of unity is required.

For part 1, write $r=a/b$ with positive integers $a,b$ and put $d=ab$. Then
$$\sqrt d=b\sqrt r.$$
The number $y=2\pi/\sqrt r$ is nonzero and satisfies
$$i\sqrt d\,y=2\pi i b,\qquad e^{i\sqrt d\,y}=1.$$
The periodic result under (15), followed by division by two, proves $\mathcal E(\pi/\sqrt r)$ for every positive rational $r$. The period calculation places each rational radicand in an integral quadratic order and gives the bound directly for the normalized value.

Finally, $\mathcal E(x)$ implies irrationality. If $x=u/v$ with $v>0$, use the exact fractions $(ku)/(kv)$ at arbitrarily large denominators in (1). Their error is zero, a contradiction. Dirichlet approximation supplies infinitely many distinct reduced approximants at exponent two. Property (1) excludes every exponent larger than two, giving $\mu(x)=2$ and completing Theorem 1.

## 8. Examples and formalization

The real family includes
$$
\frac{\log(2+\sqrt3)}{\sqrt3},\qquad
\frac{\log(2-\sqrt3)}{\sqrt3},\qquad
\frac{\log((3+\sqrt5)/2)}{\sqrt5}.
$$
The first two give opposite signs of the logarithm. The third illustrates the rational coefficients allowed by the theorem: its norm is $(9-5)/4=1$.

For an imaginary example, for every integer $k$,
$$x_k=2\arctan(1/2)+2\pi k,\qquad
e^{ix_k}=\frac35+\frac45i.$$
Part 3 applies with $d=1$, $A=3/5$, $B=4/5$. The choice $d=4$ and $x=\pi$ gives a torsion example with a nonsquarefree radicand, since $e^{2i\pi}=1$. Part 1 also allows nonintegral rational radicands, giving, for example, $\mu(\pi/\sqrt{2/3})=2$.

The Lean formalization proves the three instances of (1) under the hypotheses of Theorem 1. The principal declarations are `rational_scaled_pi_eventualLowerBound` in `PeriodicFamily/Main.lean`, the real quadratic theorem in `Quadratic/RationalFamilies.lean`, and `imaginary_quadratic_all_eventualLowerBound` in `Combined.lean`. The package documentation gives the full declaration map and reproduction commands.

The library defines its own invariant `OAI.PiExponent.irrationalityExponent`. The independent comparison specification imports only Mathlib and states the exponent-two consequence using the standard predicates
$$\operatorname{Irrational}(x)\quad\hbox{and}\quad
\forall\nu>2,\ \neg\operatorname{LiouvilleWith}(\nu,x).$$
An independently written bridge derives this proposition from (1). The verification run of October 10, 2026 rebuilt all 1,028 packaged proof modules from an initially empty build directory. We compared six statements---the three eventual bounds and their three exponent-two consequences---with an independently written Mathlib-only specification. The comparator checked the statements and referenced definitions. Nanoda and Lean's default kernel accepted the proof export, and the axiom audit found only `propext`, `Classical.choice`, and `Quot.sound`.

The run used pinned compiled dependencies for Lean and Mathlib and identified checking-tool binaries. Their identities, the verification controls, and the reproduction limits are recorded in `VERIFY.md`. Automated model reviews also examined the written argument and selected source interfaces. These checks do not establish a priority claim.

## AI use and attribution

The author initiated and directed the investigation. OpenAI coding agents contributed substantially to the mathematical development, Lean formalization, exposition, and automated reviews of the argument and its correspondence with the formalization. The work uses OpenAI's manuscript and released Lean library, the preceding logarithmic extensions, and Mathlib. These automated checks and reviews do not constitute independent human mathematical peer review or endorsement.

## References

**[O]** OpenAI, *The irrationality exponent of $\pi$ is $2$*, September 24, 2026. [Pinned manuscript and released Lean library](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026), revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The separated-weight interpolation theorem and curve-inequality proposition are in §2; the arithmetic, exact row-translation, collision, and determinant-comparison results are in §3; parameter selection is in §4. The present proof uses the precise released source interfaces identified above, including ordinary-Rees recovery and the actual global-section support bound.

**[R]** Ryan Matthew Casper, *The irrationality exponent of positive rational logarithms is 2*, October 7, 2026. [Pinned manuscript and formalization](https://github.com/Mattie/math/tree/0cfe10002ea95c45721b93d18bffbe2c3bbbcbbd/preprints/The-irrationality-exponent-of-positive-rational-logarithms-is-2-October-7-2026). The `Logarithm` modules supply distinct nonzero multiplicative centres, scaled formal jets and complex-period collision estimates. These interpolation statements themselves allow complex centres; rationality is required later by the arithmetic application, not by the geometry.

**[Q4]** Ryan Matthew Casper, *The irrationality exponent of positive quadratic logarithms is at most 4*, October 8, 2026. [Manuscript and formalization in the pinned parent collection](https://github.com/Mattie/math/tree/4aa817179b5a81358dcdefeb1d454a31ab2f2c27/preprints/The-irrationality-exponent-of-positive-quadratic-logarithms-is-at-most-4-October-8-2026). This is a distinct general bound for unnormalized logarithms, with a coarse second-embedding estimate. It is not used to infer Theorem 1.

**[M]** The mathlib Community, *Mathlib*, [revision used by the formalization](https://github.com/leanprover-community/mathlib4/tree/d13f23b723b8a846827a245b89c10fc7d3f11612). The independent endpoint specification uses its standard `Irrational` and `LiouvilleWith` predicates.
