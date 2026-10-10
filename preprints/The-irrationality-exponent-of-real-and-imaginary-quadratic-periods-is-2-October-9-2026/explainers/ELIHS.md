# How close can a fraction get?

Here are three numbers from Ryan Matthew Casper's *The irrationality exponent of real and imaginary quadratic periods is 2*, rounded to 20 decimal places:

$$
\frac{\pi}{\sqrt2}\approx2.22144146907918312351,
$$
$$
\frac{\log(3+2\sqrt2)}{\sqrt2}\approx1.24645048028046102679,
$$
$$
\frac{\arctan(\sqrt5)}{\sqrt5}\approx0.51441280099054576895.
$$

Here $\log$ means the natural logarithm. The arctangent gives the angle whose tangent is $\sqrt5$, measured in radians. You don't need to know much about either function to follow the question about fractions.

Some fractions get quite close:

| Number being approximated | Fraction | Absolute error, approximately |
|---|---:|---:|
| $\pi/\sqrt2$ | $9/4$ | $0.028558531$ |
| $\pi/\sqrt2$ | $20/9$ | $0.00078075314$ |
| $\pi/\sqrt2$ | $311/140$ | $0.000012897651$ |
| $\log(3+2\sqrt2)/\sqrt2$ | $5/4$ | $0.0035495197$ |
| $\log(3+2\sqrt2)/\sqrt2$ | $86/69$ | $0.000073668686$ |
| $\arctan(\sqrt5)/\sqrt5$ | $18/35$ | $0.00012708670$ |
| $\arctan(\sqrt5)/\sqrt5$ | $107/208$ | $0.000010275933$ |

For example, $20/9=2.2222\ldots$. It misses the first number by less than one thousandth, with a denominator of only 9. That's a useful approximation. The table also shows the usual catch: getting a smaller error tends to require a larger denominator.

We could keep adding decimal places and larger fractions. But no finite table tells us whether one of these numbers is secretly a fraction with an enormous denominator. A terminating decimal is itself a fraction, and it can agree with an irrational number for as many initial digits as we choose. Irrationality needs an argument that reaches beyond the digits we have computed.

The paper proves irrationality and then asks a stronger question: how much accuracy can fractions keep getting for the size of their denominators?

Write a fraction as $p/q$. A useful benchmark is an error of $1/q^2$. For $20/9$, that benchmark is $1/81$, about $0.01235$. Our error is much smaller. A classical result called Dirichlet's theorem says every irrational number has infinitely many distinct fractions in lowest terms whose errors are smaller than $1/q^2$.

So beating that benchmark, again and again, is something irrational numbers can always do. What happens if we demand $1/q^{2.1}$ instead? Because the exponent is larger, the allowed error is smaller. It's a harder target.

For every number covered by this paper, eventually that harder target cannot be beaten. There is a denominator threshold after which every fraction misses by at least $1/q^{2.1}$. You can replace 2.1 by 2.01, or 2.000001, or any fixed number greater than 2. Each choice gets its own threshold (and the threshold may be very large).

That combination is what “irrationality exponent two” means. The square-denominator benchmark is beaten infinitely often; every fixed higher-power benchmark is beaten only finitely often. It still allows some remarkably close fractions.

The three displayed numbers are examples of much larger families. The first family contains $\pi/\sqrt r$ for every positive rational number $r$. You can put $r=2$, $5$, or $7/3$, for instance, and the same result holds.

The second family uses numbers $A+B\sqrt d$, where $A$ and $B$ are rational and $d>1$ is a squarefree whole number. Squarefree means no square larger than 1 divides $d$: 2, 3, 5, and 6 qualify; 12 doesn't. We require

$$
A^2-dB^2=1.
$$

When $A+B\sqrt d$ is positive and different from 1, its natural logarithm divided by $\sqrt d$ has exponent two. For the example above, $A=3$, $B=2$, and $d=2$, so the required calculation is simply $9-8=1$.

The third family concerns angles. Take a positive whole number $d$ and a nonzero real number $x$. If the angle $\sqrt d\,x$ has cosine $A$ and sine $B\sqrt d$ for rational numbers $A,B$, then $x$ has exponent two. This includes angles beyond one complete turn; the actual angle matters. The arctangent example fits after doubling its angle, and dividing the resulting number by 2 preserves the conclusion.

How can a proof control infinitely many fractions? The broad idea is to suppose unusually accurate fractions continue appearing at arbitrarily large denominators, then use a carefully chosen finite collection of them to build an algebraic expression. After denominators are removed, that construction gives a nonzero integer, which must have absolute value at least 1. The assumed accuracy also forces it to be smaller than 1. Both things can't happen.

Making that construction work is the difficult part. In particular, an expression equal to zero would cause no contradiction, so the proof has to establish that its chosen determinant is nonzero. For the quadratic families it also keeps track of the two related expressions obtained by changing the sign of the square root.

The result doesn't give a usable numerical value for the denominator threshold. It also doesn't say every error is at least $1/q^2$, or some fixed positive multiple of it. What it does give is a precise answer for all three families, however far we let the denominators grow.

*The [full paper](../paper.pdf) develops the proof. Checked formal proofs and an independent automated comparison are described, with their limits and AI assistance, in the [verification record](../VERIFY.md). [Paper overview](../README.md).*
