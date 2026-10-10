# Fractions, quadratic fields, and the exponent two

Start with three actual values, rounded to 20 decimal places:

$$
\frac{\pi}{\sqrt2}\approx2.22144146907918312351,\qquad
\frac{\log(3+2\sqrt2)}{\sqrt2}\approx1.24645048028046102679,
$$
$$
\frac{\arctan(\sqrt5)}{\sqrt5}\approx0.51441280099054576895.
$$

The logarithm is natural and the angle is in radians. A few rational approximations are:

| Value | Fraction | Absolute error, approximately |
|---|---:|---:|
| $\pi/\sqrt2$ | $20/9$ | $7.8075314\times10^{-4}$ |
| $\pi/\sqrt2$ | $311/140$ | $1.2897651\times10^{-5}$ |
| $\log(3+2\sqrt2)/\sqrt2$ | $5/4$ | $3.5495197\times10^{-3}$ |
| $\log(3+2\sqrt2)/\sqrt2$ | $86/69$ | $7.3668686\times10^{-5}$ |
| $\arctan(\sqrt5)/\sqrt5$ | $18/35$ | $1.2708670\times10^{-4}$ |
| $\arctan(\sqrt5)/\sqrt5$ | $107/208$ | $1.0275933\times10^{-5}$ |

These fractions get closer as their denominators grow. That alone isn't very surprising: rounding any real number to more decimal places does the same thing. The useful question is how small the error can be *relative to the denominator*. A fraction with a million-digit denominator ought to earn its keep.

For an irrational real number $x$, its irrationality exponent $\mu(x)$ is the supremum of the exponents $\nu$ for which

$$
\left|x-\frac pq\right|<\frac1{q^\nu}
$$

holds for infinitely many distinct reduced fractions. Dirichlet's approximation theorem gives $\mu(x)\ge2$. Establishing the reverse inequality can be much harder for a specific transcendental number.

Ryan Matthew Casper's paper proves $\mu(x)=2$ throughout three families. It gives the following literal bound for each member:

$$
\forall\nu>2\ \exists Q\ge2\ \forall p\in\mathbb Z\ \forall q\in\mathbb N,
\quad q\ge Q\Longrightarrow
\left|x-\frac pq\right|\ge q^{-\nu}.
$$

Here $Q$ is a natural number, chosen before $p$ and $q$. There is no coprimality condition in this bound. The threshold may depend on $x$ and $\nu$, and the argument doesn't provide an effective value for it.

This also proves $x$ is irrational. If $x=a/b$, multiplying the numerator and denominator by arbitrarily large integers would give exact approximations beyond every proposed threshold. Their error would be zero, contradicting the positive lower bound. Once irrationality is established, Dirichlet supplies the other half of the exponent claim.

Notice why the decimal table can't do that job. Every finite decimal string agrees with some rational number, and checking a finite collection of fractions says nothing about all the denominators still to come. The table introduces the problem; the quantified bound solves it.

The periodic family is

$$
x=\frac\pi{\sqrt r},\qquad r\in\mathbb Q,\quad r>0.
$$

It's tempting to read this as “$\pi$ has exponent two, so multiplying by an algebraic number is harmless.” That would need a theorem we don't have. The proof instead uses the exponential period attached to each radicand. Writing $r=a/b$ with positive integers gives $\sqrt{ab}=b\sqrt r$, and therefore

$$
\exp\!\left(i\sqrt{ab}\,\frac{2\pi}{\sqrt r}\right)=1.
$$

This supplies a period in exactly the form the argument needs.

For the real quadratic family, let $d>1$ be squarefree, let $A,B$ be rational, and put $\alpha=A+B\sqrt d$. The conditions are

$$
\alpha>0,\qquad \alpha\ne1,\qquad A^2-dB^2=1.
$$

Then $\mu(\log\alpha/\sqrt d)=2$. The last equation is a norm condition: replacing $\sqrt d$ by $-\sqrt d$ gives a conjugate $\alpha'$ with $\alpha\alpha'=1$. Consequently the two exponentials of $x=\log\alpha/\sqrt d$ are $\alpha$ and its reciprocal. Both participate in the proof. Rational coefficients are allowed; $\alpha$ needn't be an algebraic integer.

For the imaginary family, take any positive integer $d$ and any nonzero real $x$ such that

$$
e^{i\sqrt d\,x}=A+B i\sqrt d,\qquad A,B\in\mathbb Q.
$$

Then $\mu(x)=2$. By Euler's formula, the condition says the cosine is rational and the sine is a rational multiple of $\sqrt d$. It includes every real branch satisfying the identity, not just the principal argument.

For our arctangent example, set $x=\arctan(\sqrt5)/\sqrt5$. The double-angle identity gives

$$
e^{i\sqrt5(2x)}=\frac{-2+i\sqrt5}{3}.
$$

Thus the theorem applies to $2x$, and division by the fixed integer 2 gives the result for $x$. That step matters: the coefficients at the undoubled angle aren't both rational in this presentation.

Roots of unity also fit the imaginary theorem. If the exponential has finite order $n$, then $nx$ is a nonzero real period. The periodic argument applies to $nx$, and division by $n$ returns to $x$. We keep the actual angle throughout; replacing its exponential by the principal logarithm of 1 would lose it.

The proof behind these statements assumes infinitely many excessively good approximations and constructs an interpolation matrix from a finite selection. Geometry guarantees a nonzero square minor. Clearing denominators makes its determinant integral in a quadratic order. Its nonzero integer norm supplies a lower bound, while the approximation errors supply an incompatible analytic upper bound for the same determinant. In the quadratic argument, both conjugates are retained together so that the norm estimate doesn't lose the exponent two.

This extends an inherited OpenAI proof framework to the stated families. It doesn't establish exponent two for arbitrary quadratic logarithms, and it doesn't imply a bound $|x-p/q|\ge c/q^2$ with fixed $c>0$. Exponent two still leaves room for very good occasional approximations, including ones much better than the small table above.

*See the [full paper](../paper.pdf), [overview](../README.md), and [verification record](../VERIFY.md). The record explains the checked formal proofs, independent automated comparison, inherited foundations, and substantial AI assistance; it is not a claim of human peer review.*
