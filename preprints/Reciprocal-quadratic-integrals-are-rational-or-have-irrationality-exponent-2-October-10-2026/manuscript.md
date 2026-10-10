# Reciprocal quadratic integrals are rational or have irrationality exponent 2

Ryan Matthew Casper · October 10, 2026

## Abstract

In this study, we consider integrals of the reciprocal of a quadratic polynomial. The coefficients and endpoints are rational, the interval has positive length, and the denominator stays nonzero throughout. For these integrals, there is a simple dividing line: the integral is rational exactly when the quadratic has a repeated root. In all other cases, its irrationality exponent is 2. In these irrational cases, for every $\nu>2$, every fraction $p/q$ with sufficiently large positive denominator $q$ differs from the integral by at least $q^{-\nu}$.

This proof combines elementary integration with earlier approximation results for logarithms and quadratic periods. Those results build on the methods introduced in OpenAI’s proof that the irrationality exponent of $\pi$ is 2. We apply these results to classify the integrals in this family. A Lean formalization accompanies the proof.

## 1. The classification

Let $A,B,C,a,b$ be rational numbers, and write
$$
f(t)=At^2+Bt+C,\qquad \Delta=B^2-4AC,\qquad
I=\int_a^b\frac{dt}{f(t)}.
$$
Throughout the paper we assume
$$
A\ne0,\qquad a<b,\qquad f(t)\ne0\quad(a\le t\le b).       \tag{1}
$$
The integral is an ordinary proper real integral. The denominator is continuous and has constant nonzero sign on the interval.

For an irrational real number $x$, its irrationality exponent $\mu(x)$ is the supremum of the real numbers $\nu>0$ for which
$$
0<\left|x-\frac pq\right|<q^{-\nu}
$$
holds for infinitely many reduced fractions $p/q$ with $q\ge2$. We use the following more explicit property:
$$
\begin{split}
\mathcal E(x):\quad &\forall\nu>2\;\exists N\in\mathbb N,\ N\ge2,\\
&\forall p\in\mathbb Z\;\forall q\in\mathbb N,\ q\ge N
\ \Longrightarrow\ q^{-\nu}\le\left|x-\frac pq\right|.
\end{split}                                                    \tag{2}
$$
There is no coprimality restriction in (2).

**Theorem 1.** Under (1), exactly one of the following cases holds:

1. If $\Delta=0$, then
   $$I=\frac{2}{2Aa+B}-\frac{2}{2Ab+B}\in\mathbb Q.             \tag{3}$$
2. If $\Delta\ne0$, then $\mathcal E(I)$ holds, $I$ is irrational, and $\mu(I)=2$.

Consequently,
$$
I\in\mathbb Q\quad\Longleftrightarrow\quad\Delta=0.           \tag{4}
$$

Thus the vanishing of the discriminant determines whether the value is rational or has irrationality exponent two. Its sign determines the proof of the second case. Negative discriminant gives an imaginary quadratic period; positive discriminant gives a logarithm, with different arithmetic according to whether the discriminant is a rational square.

The threshold in (2) may depend on all the fixed integral data and on $\nu$. The argument does not supply a numerical threshold, a uniform bound over the family, or a positive constant in a $q^{-2}$ lower bound.

The theorem applies only to the reciprocal of a genuine quadratic polynomial. The assumptions exclude constant or linear denominators, intervals of zero length, improper integrals, and principal values. Arbitrary polynomial numerators are outside the statement.

## 2. Approximation results used in the proof

We use three established approximation results. Each supplies property $\mathcal E$ in precisely the stated normalization.

**Rational logarithms [R].** If $r\in\mathbb Q$, $r>0$, and $r\ne1$, then $\mathcal E(\log r)$.

**Real quadratic periods [Q].** If $d>1$ is a squarefree integer, $P,T\in\mathbb Q$,
$$
P^2-dT^2=1,\qquad \alpha=P+T\sqrt d>0,\qquad\alpha\ne1,
$$
then $\mathcal E(\log\alpha/\sqrt d)$. This includes $\alpha<1$ and either sign of $T$.

**Imaginary quadratic periods [Q].** If $d$ is a positive integer, $x\ne0$ is real, and
$$
e^{i\sqrt d\,x}=P+Ti\sqrt d\qquad(P,T\in\mathbb Q),           \tag{5}
$$
then $\mathcal E(x)$. The theorem allows every real branch and includes roots of unity; $d$ need not be squarefree.

These results build on OpenAI's weighted logarithmic interpolation and determinant method [O]. The rational-logarithm extension [R] and the quadratic-period extension [Q] contain the deep approximation arguments. Here we show how the integrals in (1) fit those earlier results, with the signs and scaling needed to apply them.

We will also use rational scaling. If $n$ is a positive integer and $\mathcal E(y)$ holds, choose $2<\eta<\nu$. For sufficiently large $q$, uniformly in $p$,
$$
\left|ny-\frac pq\right|
=n\left|y-\frac{p}{nq}\right|
\ge n^{1-\eta}q^{-\eta}\ge q^{-\nu},                         \tag{6}
$$
and
$$
\left|\frac yn-\frac pq\right|
=\frac1n\left|y-\frac{np}{q}\right|
\ge\frac1nq^{-\eta}\ge q^{-\nu}.                             \tag{7}
$$
The last inequalities follow by enlarging the threshold, since $\nu-\eta>0$. Thus multiplication and division by a positive rational preserve $\mathcal E$.

Finally, $\mathcal E(x)$ implies irrationality: a rational value $x=u/v$ has exact representations $(ku)/(kv)$ with arbitrarily large denominators, contradicting (2). Dirichlet's theorem gives $\mu(x)\ge2$ for irrational $x$, and (2) excludes every exponent greater than two. Hence $\mathcal E(x)$ implies $\mu(x)=2$.

## 3. Repeated roots

Suppose $\Delta=0$. The identity
$$
(2At+B)^2=4Af(t)                                             \tag{8}
$$
and (1) show that $2At+B$ is nonzero throughout the interval. The function
$$F(t)=-\frac{2}{2At+B}$$
therefore has derivative
$$F'(t)=\frac{4A}{(2At+B)^2}=\frac1{f(t)}.$$
The fundamental theorem of calculus gives (3). Both denominators in (3) are nonzero rational numbers, so $I$ is rational. This proves the repeated-root part of Theorem 1.

## 4. Positive discriminant

Suppose $\Delta>0$, and set
$$s=\sqrt\Delta,\qquad u=2Aa+B,\qquad v=2Ab+B.$$
The identity
$$
(2At+B)^2-s^2=4Af(t)                                        \tag{9}
$$
shows that each of the affine functions $2At+B-s$ and $2At+B+s$ is nonzero on $[a,b]$. Each consequently has constant sign there. The endpoint cross-ratio
$$
\alpha=\frac{(v-s)(u+s)}{(v+s)(u-s)}                          \tag{10}
$$
is positive: it is the quotient of two positive endpoint ratios. It differs from one, because equality of the numerator and denominator would give
$$2s(v-u)=4As(b-a)=0,$$
contrary to (1) and $s>0$.

An antiderivative valid away from the roots is
$$
\frac1s\left(\log|2At+B-s|-\log|2At+B+s|\right).
$$
Evaluating it at the endpoints and using $\alpha>0$ gives
$$I=\frac{\log\alpha}{s}.                                   \tag{11}$$
The absolute values in the antiderivative permit either sign of $A$ and intervals between the roots.

### 4.1 The quadratic arithmetic

Write
$$\Delta=c^2d,$$
where $c$ is a positive rational and $d$ is a positive squarefree integer. To obtain this decomposition, write $\Delta=m/n$ with positive integers $m,n$, extract the square part $mn=k^2d$, and take $c=k/n$. Then $s=c\sqrt d$.

Set
$$
X=vu-\Delta,\qquad Y=v-u,\qquad D=X^2-\Delta Y^2.
$$
The factorization
$$D=(v^2-\Delta)(u^2-\Delta)$$
and endpoint pole avoidance show that $D\ne0$. Rationalizing (10), we obtain
$$
\alpha=P+T\sqrt d,\qquad
P=\frac{X^2+\Delta Y^2}{D},\qquad
T=\frac{2XYc}{D}.                                           \tag{12}
$$
Both coefficients are rational, and direct calculation gives
$$P^2-dT^2=1.                                               \tag{13}$$

If $d>1$, changing $\sqrt d$ to $-\sqrt d$ in (10) replaces $\alpha$ by $\alpha^{-1}$. Equation (13) is the corresponding norm-one relation in the real quadratic field. Positivity and nontriviality were already established from the integral hypotheses, so the real quadratic theorem applies to $\log\alpha/\sqrt d$. Division by the positive rational $c$ gives $\mathcal E(I)$, since
$$I=\frac1c\frac{\log\alpha}{\sqrt d}.$$

If $d=1$, the number $\alpha=P+T$ is a positive rational different from one. The rational-logarithm theorem and division by $c$ give $\mathcal E(I)$.

This proves the positive-discriminant part of Theorem 1.

## 5. Negative discriminant

Suppose $\Delta<0$, and put
$$r=-\Delta>0,\qquad s=\sqrt r,\qquad u=2Aa+B,\qquad v=2Ab+B.$$
Since
$$4Af(t)=(2At+B)^2+r,$$
the quadratic has no real zero. Direct differentiation gives the signed evaluation
$$
I=\frac2s\left(\arctan\frac vs-\arctan\frac us\right).       \tag{14}
$$
Because $v-u=2A(b-a)\ne0$ and arctangent is injective, $I\ne0$.

For a rational number $w$, define
$$p_w=\frac{r-w^2}{r+w^2},\qquad q_w=\frac{2w}{r+w^2}.$$
The double-angle formulas give
$$e^{2i\arctan(w/s)}=p_w+q_w i s.$$
Using (14), we therefore obtain
$$
e^{isI}=P+Si s,\quad
P=p_vp_u+r q_vq_u,\quad S=q_vp_u-p_vq_u,                    \tag{15}
$$
with $P,S\in\mathbb Q$.

Write $r=m/n$ with positive integers $m,n$ and set $d=mn$. Then $\sqrt d=ns$, and
$$
e^{i\sqrt d\,I}=(e^{isI})^n
=\left(P+\frac Sn i\sqrt d\right)^n\in\mathbb Q(i\sqrt d).  \tag{16}
$$
The imaginary quadratic theorem allows every real branch, so it applies directly to the nonzero value $I$ and gives $\mathcal E(I)$. This includes the torsion cases, where the exponential in (16) is a root of unity.

Sections 3--5 prove Theorem 1. In the nonzero-discriminant cases, property (2) implies irrationality and exponent two as explained in Section 2. This also proves (4).

## 6. Examples and relation to the earlier results

The repeated-root example
$$\int_1^2\frac{dt}{t^2}=\frac12$$
illustrates the rational side. For a positive square discriminant,
$$\int_{1/3}^{1}\frac{dt}{t(t+1)}=\log2.$$
The two normalized quadratic values studied in [S] appear as
$$
\int_0^1\frac{dt}{1+2t^2}=\frac{\arctan\sqrt2}{\sqrt2},
\qquad
\int_{-1}^{1}\frac{dt}{2-t^2}=\frac{\log(3+2\sqrt2)}{\sqrt2}.
$$
The second integral has negative leading coefficient and lies between the two real roots. Reversing the sign of its denominator gives a negative integral, also covered by the theorem.

The same family also contains the values $\pi/\sqrt r$ from [Q] for every positive rational $r$, as the following integral shows:
$$
\int_{-r}^{1}\frac{dt}{(t^2+r)/2}=\frac\pi{\sqrt r},          \tag{17}
$$
since $\arctan(1/\sqrt r)+\arctan\sqrt r=\pi/2$. All coefficients and endpoints in (17) are rational.

These examples explain how the classification organizes earlier constants. The real and imaginary quadratic theorem [Q] supplies the general families needed for Sections 4 and 5. The bound four for logarithms of arbitrary positive quadratic algebraic numbers [B] is a separate result: those logarithms need not have the norm-one structure and normalization used here. The normalization by $\sqrt d$ is essential to the application of the real quadratic theorem; this argument does not give exponent 2 for the corresponding unnormalized logarithm.

## 7. Formalization and verification

We formalize the integral evaluations and algebraic reductions separately from the earlier approximation theorems. The formalization proves (2) for the interval integral when $\Delta\ne0$ and then derives the exponent statement. The independent specifications use ordinary Mathlib integrals and its standard predicates `Irrational` and `LiouvilleWith`.

We used two isolated runs to build the candidate sources and compare seven statements with independently written specifications: four bound and exponent statements for the positive- and nonzero-discriminant cases, followed by the repeated-root evaluation and the rationality and irrationality equivalences. Nanoda and Lean's default kernel accepted both proof exports. Both exports contain only `propext`, `Classical.choice`, and `Quot.sound` as axioms.

The combined dichotomy and example controls passed local compilation and axiom audits, but were not additional comparison targets. Both runs reused pinned compiled dependencies; they did not rebuild all inherited sources. The accompanying verification record gives the exact statements, toolchain, retained evidence, and reproduction scope. Automated proof checks and model review are distinct from human mathematical peer review.

## AI use and attribution

The author initiated and directed the investigation. OpenAI coding agents contributed substantially to the mathematical reductions, Lean formalization, exposition, and automated reviews. The proof uses OpenAI's released interpolation and determinant theory, the author's preceding approximation results, and Mathlib. These contributions include mathematical development as well as writing and formalization.

## References

**[O]** OpenAI, *The irrationality exponent of $\pi$ is $2$*, September 24, 2026. [Manuscript and released Lean library](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026), revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

**[R]** Ryan Matthew Casper, *The irrationality exponent of positive rational logarithms is 2*, October 7, 2026. [Manuscript and formalization](https://github.com/Mattie/math/tree/0cfe10002ea95c45721b93d18bffbe2c3bbbcbbd/preprints/The-irrationality-exponent-of-positive-rational-logarithms-is-2-October-7-2026).

**[Q]** Ryan Matthew Casper, *The irrationality exponent of real and imaginary quadratic periods is 2*, October 9, 2026. [Manuscript and formalization](https://github.com/Mattie/math/tree/a93fdbe5e5aef90a9d38d805848abb07a173bfb1/preprints/The-irrationality-exponent-of-real-and-imaginary-quadratic-periods-is-2-October-9-2026). The precise family statements used here are reproduced in Section 2.

**[S]** Ryan Matthew Casper, *The irrationality exponent of arctan($\sqrt2$)/$\sqrt2$ is 2* and *The irrationality exponent of log($3+2\sqrt2$)/$\sqrt2$ is 2*, October 7, 2026. [Arctangent manuscript and formalization](https://github.com/Mattie/math/tree/a93fdbe5e5aef90a9d38d805848abb07a173bfb1/preprints/The-irrationality-exponent-of-arctan-sqrt2-over-sqrt2-is-2-October-7-2026); [logarithm manuscript and formalization](https://github.com/Mattie/math/tree/a93fdbe5e5aef90a9d38d805848abb07a173bfb1/preprints/The-irrationality-exponent-of-log-3-plus-2-sqrt2-over-sqrt2-is-2-October-7-2026).

**[B]** Ryan Matthew Casper, *The irrationality exponent of positive quadratic logarithms is at most 4*, October 8, 2026. [Manuscript and formalization](https://github.com/Mattie/math/tree/4aa817179b5a81358dcdefeb1d454a31ab2f2c27/preprints/The-irrationality-exponent-of-positive-quadratic-logarithms-is-at-most-4-October-8-2026).

**[M]** The mathlib Community, *Mathlib*, revision `d13f23b723b8a846827a245b89c10fc7d3f11612`. The independent specifications use its ordinary real-analysis and Diophantine-approximation definitions.
