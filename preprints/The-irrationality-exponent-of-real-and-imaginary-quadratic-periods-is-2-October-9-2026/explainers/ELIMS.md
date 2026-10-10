# Why these quadratic periods have exponent two

Here are three members or elementary consequences of the families in the paper, rounded to 20 decimal places:

$$
x_1=\frac\pi{\sqrt2}\approx2.22144146907918312351,
$$
$$
x_2=\frac{\log(3+2\sqrt2)}{\sqrt2}\approx1.24645048028046102679,
\qquad
x_3=\frac{\arctan(\sqrt5)}{\sqrt5}\approx0.51441280099054576895.
$$

The logarithm is natural and the arctangent is principal, in radians. Some useful fractions are:

| Target | Fraction | Absolute error, approximately |
|---|---:|---:|
| $x_1$ | $20/9$ | $7.8075314\times10^{-4}$ |
| $x_1$ | $311/140$ | $1.2897651\times10^{-5}$ |
| $x_2$ | $86/69$ | $7.3668686\times10^{-5}$ |
| $x_2$ | $263/211$ | $4.9826501\times10^{-6}$ |
| $x_3$ | $18/35$ | $1.2708670\times10^{-4}$ |
| $x_3$ | $107/208$ | $1.0275933\times10^{-5}$ |

Finite calculations can illustrate the denominator/error tradeoff, but they can't establish even irrationality. Each displayed decimal interval contains rational numbers. Ryan Matthew Casper's *The irrationality exponent of real and imaginary quadratic periods is 2* addresses the infinite question: which powers of the denominator can rational approximation beat infinitely often?

For an irrational $x$, define $\mu(x)$ as the supremum of $\nu$ such that $|x-p/q|<q^{-\nu}$ holds for infinitely many reduced fractions. Dirichlet gives the lower bound two. The work here is to show, for each $x$ in the stated families,

$$
\forall\nu>2\ \exists Q\in\mathbb N,\ Q\ge2:\quad
\forall p\in\mathbb Z\ \forall q\in\mathbb N,\quad
q\ge Q\Longrightarrow q^{-\nu}\le\left|x-\frac pq\right|.
$$

No reduction condition is needed in this formulation. It also establishes irrationality directly: a rational $x$ would admit zero-error representations at unbounded denominator multiples. Dirichlet then turns the eventual bounds into $\mu(x)=2$.

The real quadratic statement has a specific normalization. For squarefree integer $d>1$ and rational $A,B$, suppose

$$
\alpha=A+B\sqrt d>0,\qquad \alpha\ne1,\qquad A^2-dB^2=1.
$$

Then $x=\log\alpha/\sqrt d$ satisfies the bound. We allow $0<\alpha<1$ as well as $\alpha>1$, and rational denominators in $A,B$. This is not restricted to integral units or fields with a particular class number.

The norm condition provides the second exponential identity for free:

$$
e^{\sqrt d\,x}=\alpha,\qquad
e^{-\sqrt d\,x}=\alpha'=\alpha^{-1}.
$$

For $\alpha=3+2\sqrt2$, it is the elementary equality $9-8=1$. The square-root divisor is part of the result, not an optional adjustment to its notation. There is no general invariance of irrationality exponent under algebraic multiplication that would let us discard it.

The imaginary statement is broader in its radicand: for any positive integer $d$, if $x\ne0$ is real and

$$
e^{i\sqrt d\,x}=A+B i\sqrt d\quad(A,B\in\mathbb Q),
$$

then $\mu(x)=2$. Complex conjugation supplies the identity with the negative generator. Every real branch is included. This is a direct application to each actual $x$ satisfying the exponential identity; it isn't an appeal to preservation under adding an algebraic multiple of $\pi$.

For $x_3$ above, the appropriate identity is

$$
e^{i\sqrt5(2x_3)}=\frac{-2+i\sqrt5}{3}.
$$

Apply the theorem to $2x_3$ and then divide by 2. To see why fixed integer division is harmless for the eventual bound, suppose $y$ has that bound and consider $y/n$. For a desired exponent $\nu>2$, choose $2<\mu<\nu$. Applying the bound for $y$ to $np/q$ gives

$$
\left|\frac yn-\frac pq\right|\ge \frac1n q^{-\mu}\ge q^{-\nu}
$$

once $q$ is sufficiently large. There's room between the two exponents to absorb the fixed factor.

The third statement is the periodic family $\mu(\pi/\sqrt r)=2$ for every positive rational $r$. Write $r=a/b$ with positive integers and take the integral generator $\beta=i\sqrt{ab}$. Then $2\pi/\sqrt r$ is an actual nonzero real period for $e^{\beta x}$, since its product with $\beta$ is $2\pi i b$. The period theorem and fixed integer division finish this case.

This periodic argument also closes the torsion case of the imaginary theorem. If $e^{i\sqrt d x}$ has finite order $n$, then $nx\ne0$ and $e^{i\sqrt d(nx)}=1$. The period is retained as a real number. Taking a principal logarithm of 1 would erase precisely the quantity we need.

The proof mechanism is a determinant contradiction. Fix $\nu>2$ and suppose there are approximations of quality $q^{-\nu}$ at arbitrarily large denominators. After choosing parameters depending on the target and this actual $\nu$, select a finite approximation sequence and build a weighted interpolation problem. The inherited geometry produces a surjective coefficient map, hence a nonzero full-row minor at sufficiently large degrees.

Now clear the rational centers and truncated-logarithm denominators in that exact minor. The resulting determinant belongs to an integral quadratic order. In the real quadratic case, its two embeddings give a product that is a nonzero integer. Thus their absolute-value product is at least one. In the imaginary periodic case, the elementary norm $a^2+Db^2$ provides the corresponding arithmetic estimate.

The analytic estimate uses those same selected rows and columns. Expanding around the true exponential relation brings in the small errors $p_i/q_i-x$. Their smallness forces an upper bound incompatible with the arithmetic lower bound. It's essential that the minor be nonzero, and that both conjugates concern the same algebraic determinant. Two unrelated determinants would not supply the norm identity we are using.

The generalization also has to pay for the generator's size and for rational coefficient denominators. These are fixed costs once the family member is fixed. The parameter margins absorb them without a degree-two loss in the final exponent. In particular, the extra analytic cost from the generator is matched in the arithmetic estimate; simply bounding one conjugate crudely would miss the useful feature of the argument.

The result is pointwise, with no effective $Q$ or uniform bound as the radicand varies. It also does not assert bad approximability: $\mu(x)=2$ needn't give a positive constant $c$ with $|x-p/q|\ge c/q^2$, or bounded continued-fraction coefficients. The families extend earlier individual examples using an inherited OpenAI framework, rather than supplying a new foundation for every part of the method.

*The [paper](../paper.pdf) contains the detailed argument. The [verification record](../VERIFY.md) describes checked formal proofs, the independent automated specification comparison, AI assistance, and the remaining assurance limits. [Overview](../README.md).*
