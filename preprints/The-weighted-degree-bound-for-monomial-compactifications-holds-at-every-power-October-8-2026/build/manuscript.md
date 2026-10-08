# The weighted degree bound for monomial compactifications holds at every power

Ryan Matthew Casper  
October 8, 2026  

## Abstract

Let a finite monomial embedding contain the constant monomial and every ordinary coordinate, and suppose each embedding monomial has nonnegative weighted degree at most $R$. Every section of the $n$-th power of the induced hyperplane bundle then has affine polynomial coefficients of weighted degree at most $nR$, for every integer $n\geq0$. The assertion holds in every frame of that bundle on the fixed affine chart. We obtain it from the existing eventual coefficient bound by a tensor-power argument. This supplies a separate strengthening of an intermediate lemma used by the rational-logarithm, rational-arctangent, and two normalized quadratic-period preprints. Their proofs and endpoint statements need no revision.

## 1. Setting and statement

Let $K$ be a field and let $x_1,\ldots,x_d$ be coordinates on affine space. Choose a finite indexed family $(\alpha_j)_{j\in J}$ of exponents in $\mathbb N^d$ containing $0,e_1,\ldots,e_d$, where $e_i$ is the $i$-th coordinate vector. Repeated exponents are harmless. Let $X$ be the scheme-theoretic projective closure of the monomial morphism

$$
x\longmapsto [x^{\alpha_j}]_{j\in J}.
$$

Concretely, put $S=K[t x^{\alpha_j}:j\in J]\subset K[x_1,\ldots,x_d,t]$, graded by the exponent of $t$, so each displayed generator has degree one. Then $X=\operatorname{Proj}S$. This specifies the scheme over every field, including finite fields. Let $L$ be the induced hyperplane bundle. The chart where the coordinate indexed by a chosen zero exponent is nonzero is affine $d$-space. Write $s_0$ for that coordinate section of $L$; it is invertible on this chart.

Fix real weights $w_i\geq0$ and a real number $R$ such that

$$
w\cdot\alpha_j=\sum_i w_i(\alpha_j)_i\leq R
\quad\text{for every }j\in J.
$$

For a polynomial $f$, the bound $\deg_w f\leq C$ means that every exponent $\alpha$ with nonzero coefficient in $f$ satisfies $w\cdot\alpha\leq C$. This support formulation includes the zero polynomial without a special degree convention.

**Theorem.** For every integer $n\geq0$ and every section $s\in H^0(X,L^n)$, the polynomial

$$
f=\left.s/s_0^n\right|_{\mathbb A^d}
$$

satisfies $\deg_w f\leq nR$. The same support bound holds for the coefficient of $s$ in every frame of $L$ on this fixed affine chart.

The last clause allows a change of the bundle frame. The affine coordinates remain fixed. We assert neither projective normality nor a converse saying that every polynomial within the degree budget extends to a section.

## 2. Proof by taking powers

The existing coefficient theorem for this exact compactification provides an integer $N$ such that every section of $L^m$, in every affine frame, has weighted polynomial coefficients bounded by $mR$ whenever $m\geq N$. We use that established theorem as an input.

For nonzero polynomials over a field,

$$
\deg_w(fg)=\deg_w f+\deg_w g,
\qquad \deg_w(f^k)=k\deg_w f.
$$

To see why cancellation cannot spoil the equality, order exponents first by weighted degree and then by a lexicographic order. Each finite polynomial support has a largest exponent in this order. The largest exponent of a product is the sum of the largest exponents of its factors, and its coefficient is the product of two nonzero coefficients. The field assumption makes that coefficient nonzero. The formal proof uses this tie-breaking order directly.

First suppose $n>0$. Choose a positive integer $k$ with $nk\geq N$. The tensor power $s^k$ is a section of $L^{nk}$, with coefficient $f^k$ in the induced frame. The eventual coefficient bound gives

$$
k\deg_w f=\deg_w(f^k)\leq nkR.
$$

Division by $k$ gives $\deg_w f\leq nR$. The zero polynomial already has the required support bound.

For $n=0$, let $s$ be a global regular function and let $f$ be its restriction to the affine chart. For every positive integer $k$, the product $s^k s_0$ is a section of $L$. The positive-power case just proved applies at bundle degree one, so

$$
k\deg_w f=\deg_w(f^k)\leq R.
$$

If $\deg_w f>0$, the left side exceeds $R$ for sufficiently large $k$. Thus $\deg_w f\leq0$. This proves the degree-zero case without assuming that an arbitrary line bundle has a nonzero positive-degree section: here the needed section is the actual constant-coordinate section $s_0$.

Finally, any two frames on this affine chart differ by a unit in $K[x_1,\ldots,x_d]$. Such a unit is a nonzero constant. Multiplication by it preserves the polynomial support, so the bound holds in every frame. In Lean, the tensor and restriction isomorphisms can introduce these unit factors; the proof accounts for them explicitly.

## 3. Connection with the four existing preprints

The common construction in those preprints uses positive rational weights and a scaled monomial collection. It includes the constant and ordinary coordinate monomials, and its existing exponent-budget theorem verifies $w\cdot\alpha\leq R$. It therefore satisfies the hypotheses above.

The new result removes the *degree-bound* threshold: once a global section exists, its polynomial coefficient has the required weighted support at every bundle power. The interpolation argument still uses eventual surjectivity of global jet restriction. This note supplies no numerical bound for that threshold, no effective irrationality constant, and no additional irrationality-exponent endpoint.

The earlier eventual degree statements remain true. Their source files, manuscripts, exported proof artifacts, and recorded checker evidence can remain as they are. This note can be cited as an optional strengthening; it is not needed to repair the previous arguments. The same formal result also applies to the admissible compactification in the released π library.

## 4. Formal statement and scope

The accompanying Lean files keep the new declarations separate from the inherited library:

| Mathematical assertion | Lean declaration |
|---|---|
| Recover a bound from a positive polynomial power | `Degree.supportBound_of_pow` |
| Every positive bundle power | `Degree.positive_supportBound` |
| Power zero, using an invertible coordinate section | `Degree.zero_supportBound` |
| Every power of the exact monomial compactification | `Degree.monomial_all_supportBound` |
| The actual construction shared by the four preprints | `Degree.logarithm_all_supportBound` |
| The original π library's admissible construction | `Degree.admissible_all_supportBound` |

The abstract positive-power lemma assumes the existing eventual coefficient bound. The concrete monomial theorem discharges that assumption with `OAI.PiExponent.WeightedGlobalSectionBound.eventual_supportBound` and constructs the section needed at power zero. Its numerical hypotheses are the nonnegativity of the weights and the finite list of monomial budget inequalities; it does not assume the conclusion at small powers.

This is a reusable formal strengthening obtained by a standard tensor-power argument. We make no claim that the underlying mathematical principle is new. Verification results, source identities, and reproduction instructions accompany this note.

## AI use and attribution

The author initiated and directed the investigation of simplifying the degree-bound step in the earlier interpolation arguments. OpenAI coding agents contributed substantially to developing this reference note, producing its Lean formalization, and conducting an independent automated adversarial review. The construction builds on OpenAI's released manuscript and π library, the rational-logarithm extension, and Mathlib. Automated checking and model review are distinct from independent human mathematical review.

## References

1. OpenAI, *The irrationality exponent of π is 2*, manuscript dated September 24, 2026, and [released source pinned to commit adc7f124](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026). The imported eventual coefficient theorem and the tensor, section, and frame interfaces come from this development.
2. Ryan Matthew Casper, *The irrationality exponent of positive rational logarithms is 2*, October 7, 2026. [Manuscript and proof package](https://github.com/Mattie/math/tree/main/preprints/The-irrationality-exponent-of-positive-rational-logarithms-is-2-October-7-2026).
3. Ryan Matthew Casper, *The irrationality exponent of nonzero rational arctangents is 2*, October 7, 2026. [Manuscript and proof package](https://github.com/Mattie/math/tree/main/preprints/The-irrationality-exponent-of-nonzero-rational-arctangents-is-2-October-7-2026).
4. Ryan Matthew Casper, *The irrationality exponent of arctan(sqrt(2))/sqrt(2) is 2*, October 7, 2026. [Manuscript and proof package](https://github.com/Mattie/math/tree/main/preprints/The-irrationality-exponent-of-arctan-sqrt2-over-sqrt2-is-2-October-7-2026).
5. Ryan Matthew Casper, *The irrationality exponent of log(3+2sqrt(2))/sqrt(2) is 2*, October 7, 2026. [Manuscript and proof package](https://github.com/Mattie/math/tree/main/preprints/The-irrationality-exponent-of-log-3-plus-2-sqrt2-over-sqrt2-is-2-October-7-2026).
6. The Mathlib community, [Mathlib source](https://github.com/leanprover-community/mathlib4). The polynomial argument uses the leading-support results in `Mathlib.Algebra.MonoidAlgebra.Degree`.
