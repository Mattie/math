# Rational logarithms: an explanation for a PhD student in another field

This is a companion to Ryan Matthew Casper’s *The irrationality exponent of positive rational logarithms is 2* (October 7, 2026). Read the [paper](../paper.pdf) or its [TeX manuscript](../build/main.tex) for the full argument. The discussion assumes comfort with proofs and asymptotics, but no background in Diophantine approximation or algebraic geometry.

## The quantitative question

An irrationality proof excludes equality with a rational number. It need not say how close rational numbers can get. For example, knowing that $\log 2$ is irrational does not distinguish between infinitely many errors of size $q^{-2}$ and infinitely many of size $q^{-10}$. Those are quite different approximation behaviors.

The denominator is the relevant measure of complexity. The approximation $7/10$ to $\log 2\approx0.69314718$ has error about $0.00685$, below $10^{-2}$. The approximation $9/13$ has error about $0.00083949$, below $13^{-2}\approx0.005917$, but above $13^{-3}\approx0.000455$. A few such examples illustrate the scale; they cannot determine the asymptotic answer.

For an irrational real number $x$, its irrationality exponent is

$$
\mu(x)=\sup\{\nu:\ 0<|x-p/q|<q^{-\nu}
\text{ for infinitely many distinct reduced }p/q,\ q>0\}.
$$

Dirichlet approximation gives $\mu(x)\ge2$. The hard direction in this paper is the upper bound. For every rational $a>0$, $a\ne1$, it proves

$$
\forall\nu>2\quad\exists Q\ge2\quad
\forall p\in\mathbb Z\quad\forall q\in\mathbb Z,\ q\ge Q:\qquad
\left|\log a-\frac pq\right|\ge q^{-\nu}.
$$

Here $Q$ may depend on $a,\nu$, and the assertion includes unreduced fractions. That last feature also proves irrationality: if $\log a=u/v$, the exact representations $ku/(kv)$ would violate the bound for arbitrarily large denominators. Dirichlet then supplies the other inequality.

The conclusion concerns natural logarithms individually, including negative values when $0<a<1$. It says nothing about the exponent of $\log2/\log3$. Nor does it give a positive constant $c$ with error always at least $c/q^2$, bounded continued-fraction coefficients, or an explicit threshold $Q$.

## Where the method comes from

OpenAI’s September 24, 2026 preprint, [*The irrationality exponent of π is 2*](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026), is the stated source of the weighted logarithmic interpolation and determinant method used here. Its released Lean library supplies substantial geometric and analytic machinery. The present paper extends that framework to a family of logarithms; the theorem about π alone does not imply this family result.

In the π construction, the exact points are the complex periods $2\pi i j$, where $e^{2\pi i j}=1$. Rational approximations to π supply nearby centers with first coordinate 1 and different remaining coordinates; the matrix lies over $\mathbb Q(i)$. The logarithm extension instead uses varying rational first coordinates and a rational matrix. This changes the interpolation hypothesis, rather than merely substituting a different constant into the final theorem.

The useful connection is exponential geometry. On the graph

$$
(Y,X_1,\ldots,X_m)=(e^z,z,\ldots,z),
$$

the logarithm governs local coordinates. If $\xi=\log a$, the points at $z=j\xi$ have rational exponential coordinates $a^j$. Replacing $\xi$ with excellent rational approximations produces rational centers very close to that graph. The proof makes a determinant simultaneously arithmetically nonzero and analytically too small.

## Why the interpolation step needs geometry

Assume, for contradiction, arbitrarily large $q$ admit errors at most $q^{-\nu}$ for a fixed $\nu>2$. Select finitely many approximations $r_i=p_i/q_i$ with sufficiently separated denominators. The centers are

$$
b_j=(a^j,jr_1,\ldots,jr_m),\qquad 0\le j<K.
$$

Their first coordinates are distinct because $a>0$ and $a\ne1$. Near a center, set

$$
t=Y/a^j-1,\qquad u_i=X_i-jr_i-\log(1+t).
$$

A *jet* is a finite collection of coefficients of a local power series, generalizing a value and several derivatives. The paper uses weighted jets: coefficients $t^su^\beta$ are retained according to a weighted cutoff. The weights let the different denominator sizes enter the construction at different costs.

Interpolation asks whether polynomials of controlled weighted degree can prescribe all these coefficients independently. Dimension counting alone cannot show this; conditions may have hidden dependencies. The paper proves surjectivity for every sufficiently large height in an integer sequence $H=nR$.

The geometric obstruction would be a curve having too much contact with the prescribed jets relative to its degree. A curve estimate excludes that obstruction. A substantial inherited comparison lemma controls the normal directions of persistent common zero sets of derivatives. The logarithm-specific rigidity argument then uses

$$
dX_i=dY/Y.
$$

On a smooth complete algebraic curve, an exact differential has zero residues, whereas $dY/Y$ records orders of zeros and poles of $Y$. This forces $Y$ to be constant in the relevant case. A constant-$Y$ curve meets at most one center, where a zero/pole comparison finishes the estimate.

To pass from curves to interpolation, the proof compactifies the ambient space and blows up the ideals encoding the jets. A blowup is a geometric construction that turns these local vanishing requirements into a divisor. The curve estimate, together with a separate ample divisor, supplies ampleness of the required divisor. Ampleness is a positivity property ensuring that sufficiently high powers of the associated line bundle provide a projective embedding. Serre vanishing removes the cohomological obstruction to prescribing local data, yielding the desired surjection onto finite local quotients. The manuscript carefully uses eventual ordinary powers of the ideal and recovers a polynomial degree bound. Neither an unrestricted Chinese remainder theorem nor strict positivity on curves alone would complete this step. See [the interpolation section](../build/sections/interpolation.tex).

## One determinant, two incompatible estimates

Interpolation gives a rational matrix of full row rank, hence a nonzero square minor $\Delta_H$. Its entries come from coefficients of

$$
\bigl(a^j(1+t)\bigr)^h
\prod_i\bigl(jr_i+G_i(t)+u_i\bigr)^{\alpha_i},
$$

where $G_i$ is a finite logarithm series. The factor $a^{jh}$ matters.

Arithmetic gives a lower bound. Writing $a=n/d$, suitable row and column scalings, together with least common multiples clearing the denominators in $G_i$, turn the determinant into a nonzero integer. Its absolute value is at least one. Undoing the scaling bounds how small $\Delta_H$ can be; the rational base adds a cost involving $K\log d/w_0$, where $w_0$ is the degree weight of $Y$.

Analysis gives an upper bound for the same minor. Expand its rows using entire functions obtained by substituting $(e^z,z+u_1,\ldots,z+u_m)$ into the column polynomials. The expansion has two possibilities. Many rows with the same auxiliary index require distinct Taylor orders to avoid identical rows; this forces decay. Otherwise many rows carry large powers of the small approximation errors, which also force decay. The proof controls truncation, convergence and the number of expansion choices.

Parameters are chosen in a strict order: fix $a,\nu$, choose the finite dimension and global parameters, then select the approximations and their denominator-dependent weights. Only after all these choices does $H=nR$ grow. This absorbs both the denominator cost and the analytic cost associated with $|\log a|$. The upper bound eventually contradicts the lower bound in either case. These distinct-center interpolation and cost estimates are the substance of the extension. See [the determinant estimates](../build/sections/determinant.tex) and [parameter selection](../build/sections/conclusion.tex).

## Reading the verification evidence

The [endpoint](../lean/Logarithm/Main.lean) has the stated rational-input theorem and explicit quantified approximation bound without separate irrationality or interpolation assumptions. The [verification report](../lean/VERIFICATION.md) records a Lean 4.34.1 build, Nanoda checking of the exported dependency closure, and replay in a fresh Lean 4.34.0 kernel. Audits found only propositional extensionality, classical choice and quotient soundness among the axioms used. Negative controls tested rejection of a forbidden axiom and an ill-typed proof.

These checks concern proof terms and definitions, not numerical samples of logarithms. A separately formulated [statement bridge](../review/blind-statement/CertifiedBridge.lean) checks agreement with the advertised bound; it is not an independent mathematical reproof. Formal checking does not establish priority or certify every sentence of this exposition. The report claims no external human peer review.

The author, Ryan Matthew Casper, initiated and directed the extension. OpenAI coding agents contributed substantially to the candidate argument, Lean formalization and automated adversarial reviews, and assisted with these companion explanations. The source manifest distinguishes 55 extension modules from 869 unchanged OpenAI modules. That inherited work is a substantial part of the proof, and its attribution is essential to understanding what was added.
