# The family theorem and the determinant argument

Ryan Matthew Casper's *The irrationality exponent of real and imaginary quadratic periods is 2* proves exponent two for three families of real numbers. The common conclusion is stronger to read in its literal approximation form than as a statement about a supremum. For each target $x$,

$$
\forall\nu>2\ \exists Q\in\mathbb N,\ Q\ge2:\quad
\forall p\in\mathbb Z\ \forall q\in\mathbb N,\quad
q\ge Q\Longrightarrow
q^{-\nu}\le\left|x-\frac pq\right|.
\tag{1}
$$

The order of these quantifiers matters. The threshold precedes both numerator and denominator, and the fractions need not be reduced. An exact rational value would violate (1) along denominator multiples, so irrationality follows. Dirichlet approximation then gives the lower endpoint two for the conventional irrationality exponent, while (1) excludes every larger exponent.

The family statements are:

1. For every rational $r>0$, $x=\pi/\sqrt r$ satisfies (1).
2. For every squarefree integer $d>1$ and rational $A,B$ with $A^2-dB^2=1$, if $\alpha=A+B\sqrt d>0$ and $\alpha\ne1$, then $x=\log\alpha/\sqrt d$ satisfies (1).
3. For every positive integer $d$ and nonzero real $x$, if $e^{i\sqrt d\,x}=A+B i\sqrt d$ for rational $A,B$, then $x$ satisfies (1).

In the second family, rational coefficients are intentional. No integrality, unique factorization, or class-number condition is imposed. In the third, neither squarefreeness nor a non-torsion condition is imposed, and every real branch satisfying the exponential identity is covered.

For orientation, these statements give exponent two for $\pi/\sqrt2$ and $\log(3+2\sqrt2)/\sqrt2$. They also give it for $x=\arctan(\sqrt5)/\sqrt5$, using

$$
e^{i\sqrt5(2x)}=\frac{-2+i\sqrt5}{3}
$$

and then dividing by 2. The theorem applies directly to the doubled angle in this presentation. Numerical approximants are useful illustrations, but no finite digit calculation or list of fractions establishes (1).

The normalization by the square root is essential to the theorem being claimed. One cannot remove it by assuming that multiplication by an arbitrary algebraic number preserves irrationality exponent. Likewise, the all-branches statement is obtained from each literal exponential identity, not from a general preservation result under adding algebraic multiples of $\pi$. These are small-looking distinctions that change the mathematical claim substantially.

The proof adapts an inherited OpenAI interpolation and determinant framework. The arithmetic and analytic parts must concern one and the same selected minor. That requirement is easy to understate in a sketch, so it's useful to follow the construction in that order.

Fix $\nu>2$ and suppose there are excessively good rational approximations at unbounded denominators. The parameter construction is performed for this actual $\nu$; it doesn't first replace it by $\nu/2$. Fix the field data and analytic radius as well, then select the finite approximation sequence used in the interpolation problem. The eventual growth variable is the common polynomial degree, with those choices held fixed.

The geometric input provides surjectivity for a coefficient map with prescribed weighted jets and controlled polynomial support. Its support bound and packet bound use the same final degree scale. Consequently there is a nonzero full-row minor at arbitrarily large scales. A comparison ample power used within the geometric argument does not enlarge the final column budget. This is where the construction gets an actual determinant to estimate; a dimension heuristic or a generic full-rank assertion would not be enough.

The entries are coefficients of explicit polynomial and truncated-logarithm expressions at the chosen rational centers. Clearing denominators puts the selected determinant in an integral quadratic order. The clearing identities retain the inverse row factors: the relevant powers have the form $q_i^{\gamma_i-b_i}$, when $b_i\le\gamma_i$, rather than simply $q_i^{\gamma_i}$. Discarding that saving changes the leading arithmetic estimate. Least common multiples clear the truncated logarithms, and a common denominator for the rational algebraic endpoint adds a fixed column-clearing cost.

For the quadratic argument, write the integral generator as $\beta$, with its other embedding $-\beta$. Both embedded matrices come from the same order-valued matrix, with the same selected minor. If its cleared determinant is $\Delta\ne0$, its norm is a nonzero integer, and therefore

$$
\left|\sigma_+(\Delta)\sigma_-(\Delta)\right|\ge1.
$$

Taking the average of the two logarithmic estimates retains leading arithmetic cost one in the proof's normalization. The useful feature is the paired treatment of the conjugates. A coarse estimate for an otherwise uncontrolled conjugate can lose exactly the strength needed to reach exponent two.

For real $d$, the norm-one hypothesis provides the paired exponential identities

$$
e^{\sqrt d\,x}=\alpha,\qquad e^{-\sqrt d\,x}=\alpha^{-1}.
$$

They hold also when $0<\alpha<1$. For imaginary $d$, conjugating the supplied exponential identity provides the negative-generator identity. In the non-torsion case the endpoint's power sequences are injective, as required by that interpolation construction.

The analytic side expands the same nonzero determinant using the errors between the rational centers and the true exponential relation. Translation and collision estimates give two possible upper-bound contributions. Parameter margins make each incompatible with the arithmetic lower bound when the common degree is sufficiently large. The strict gap is available for every fixed $\nu>2$, which is what yields (1), rather than just a bound at one larger exponent.

Generalizing the generator introduces a size parameter $M\ge\max(1,|\beta|)$ and $\lambda=\log M$. The true slope error is multiplied by $\beta$, so its analytic estimate acquires a fixed $\lambda$ cost. The arithmetic reserve is enlarged correspondingly. At the normalized level, the extra analytic term $\lambda/w_*$ is canceled by an improvement of the same size in the arithmetic error allowance, where $w_*$ is the least approximation weight. This is a real piece of the generalization: treating the generator size only as analytic overhead would weaken the conclusion. The rational endpoint denominator is another fixed cost paid by the parameter choice.

The periodic argument has multiplicative centers equal to 1, but keeps a nonzero real period $\xi$ with $e^{i\sqrt D\xi}=1$. Its order $\mathbb Z[\sqrt{-D}]$ has the elementary norm

$$
N(a+b\sqrt{-D})=a^2+Db^2.
$$

A nonzero element has modulus at least one. This works for every positive integer $D$, without squarefreeness. For rational $r=a/b>0$, choose $D=ab$ and $\xi=2\pi/\sqrt r$; then $i\sqrt D\xi=2\pi i b$. Applying the periodic theorem and dividing by 2 proves the first family.

It also completes the imaginary family when the algebraic endpoint is torsion. If its order is $n>0$, the actual real number $nx$ is a nonzero period. Apply the periodic theorem to $nx$ and divide by $n$. Fixed integer division preserves (1): use an intermediate exponent $2<\mu<\nu$ and absorb the factor $n$ into the denominator threshold. No classification of quadratic roots of unity is needed for this reduction. Replacing the actual period by a principal logarithm of 1 would instead give zero and destroy the argument.

The conclusion remains pointwise and non-effective. No uniform threshold in the radicand or discriminant is supplied, and no estimate $c/q^2$ with fixed $c>0$ is established. Thus exponent two does not imply bounded continued-fraction coefficients. Nor does this theorem turn an earlier upper bound for unnormalized positive quadratic logarithms into an exponent-two result for every such logarithm.

The contribution is the adaptation and family generalization within the inherited framework. Its geometric, cohomological, collision, and lattice foundations are reused; this explainer is not a reconstruction of them. The [full paper](../paper.pdf) makes the argument and its dependencies available for closer examination.

*The formal results compiled, and an independent specification comparison with kernel checking passed on October 9, 2026. The [verification record](../VERIFY.md) gives the scope, artifact identities, inherited-foundation limits, and substantial OpenAI assistance. This is automated assurance, not human peer review or a priority claim. [Paper overview](../README.md).*
