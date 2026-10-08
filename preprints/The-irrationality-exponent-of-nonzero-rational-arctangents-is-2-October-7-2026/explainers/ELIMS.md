# Fractions, arctangents, and a useful point on the unit circle

Here's our angle, measured in radians and rounded to 20 decimal places:

$$
\arctan(1/2) \approx 0.46364760900080611621.
$$

Here are a few fractions that approximate its value:

| Fraction | Decimal value (rounded) | Error (approximately) |
|---|---:|---:|
| $58/125$ | 0.464000000000 | 0.000352390999 |
| $51/110$ | 0.463636363636 | 0.000011245364 |
| $338/729$ | 0.463648834019 | 0.000001225018 |
| $389/839$ | 0.463647199046 | 0.000000409954 |

The fraction $51/110$ gets closer than $58/125$, even with a smaller denominator. We'd like to understand how far that sort of improvement can go. There's a useful surprise waiting for us: if $x=\arctan(1/2)$, then $e^{2ix}=(3+4i)/5$, so the angle gives us exact rational coordinates to work with.

The displayed decimals are rounded; none of these fractions equals the irrational value exactly.

This is an explanation of Ryan Matthew Casper's [*The irrationality exponent of nonzero rational arctangents is 2*](../paper.pdf), dated 7 October 2026. The [manuscript](../build/manuscript.md) has the full argument.

Let's first be clear about what we'd like from an approximation. Writing down another decimal place is easy; the denominator just gets another factor of ten. The more interesting question is whether we can keep finding fractions whose errors are smaller than $1/q^2$, or $1/q^{2.01}$, where $q$ is the denominator in lowest terms.

Dirichlet's approximation theorem gives every irrational number infinitely many fractions with error below $1/q^2$. The *irrationality exponent* tells us how far we can increase that power and still have infinitely many successful fractions. Formally, it's the supremum of the positive $\nu$ for which

$$
0<|x-p/q|<q^{-\nu}
$$

holds for infinitely many reduced fractions.

The paper proves that $\arctan r$ is irrational and has exponent exactly 2 whenever $r$ is a nonzero rational number. So $1/2$ is an example, and the same conclusion holds for $2$, $-3/5$, or any other allowed input. For every fixed $\varepsilon>0$, eventually

$$
|\arctan r-p/q|\ge q^{-(2+\varepsilon)}
$$

for every numerator $p$. Here the denominator threshold depends on $r$ and $\varepsilon$.

You can make $\varepsilon$ as small as you like, but the threshold comes with it. We don't get a single positive constant $c$ with error always at least $c/q^2$ by letting $\varepsilon$ go to zero. And we are talking about radian values throughout. ($\arctan1$ is irrational as $\pi/4$ radians and rational as 45 degrees. Units are unusually consequential in this question.)

## Why try this after π?

OpenAI's [paper on the irrationality exponent of π](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026) supplied a weighted interpolation and determinant method. The rough plan is quite appealing: suppose there are too many excellent fractions, build a nonzero determinant from them, and show that it would have to be smaller than its arithmetic permits.

Our preceding [rational-logarithm paper](../../The-irrationality-exponent-of-positive-rational-logarithms-is-2-October-7-2026/README.md) adapted that method to $\log a$ for positive rational $a\ne1$. There, $e^{j\log a}=a^j$ gives distinct rational coordinates at which to interpolate. That extension provides the more general interpolation geometry used here.

For an angle, we can use

$$
\vartheta=2\arctan r,\qquad
\alpha=e^{i\vartheta}
=\frac{1+ir}{1-ir}
=\frac{1-r^2}{1+r^2}+i\frac{2r}{1+r^2}.
$$

Both coordinates are rational. Substitute $r=1/2$ and you get $\alpha=(3+4i)/5$, a point on the unit circle. Its powers stay in $\mathbb Q(i)$, so they give us exact arithmetic at successive multiples of the angle. That's a promising place to try the earlier construction, though it leaves some fairly important details to fix.

One is whether the powers repeat. The rational-coordinate roots of unity are only $1,-1,i,-i$. A short algebraic-integer argument proves this: twice each coordinate must be an integer, and the squares of those two integers add to 4. In our family, repetition occurs only for $r=0,\pm1$. We'll leave zero out and return to $\pm1$ below.

## Following the determinant

Suppose we have approximations $p_k/q_k$ to $\vartheta$ with errors at most $q_k^{-\nu}$, for a fixed $\nu>2$, at arbitrarily large denominators. Choose finitely many with large, well-separated denominators. The interpolation centers have coordinates

$$
(\alpha^j,ij p_1/q_1,\ldots,ij p_m/q_m).
$$

The $i$ here is the imaginary unit; $k$ indexes the approximations, and $j$ runs from 0 to $K-1$ for $K$ centers.

Think of Hermite interpolation, where you prescribe values and derivatives, except that we now have several variables and different limits on their degrees. A weight of roughly $\log q_k$ goes on the $k$-th additive variable. This is useful because raising its denominator to a power later contributes that power times $\log q_k$ to our size estimate.

The needed interpolation theorem says we can prescribe all the selected Taylor coefficients with polynomials inside the weighted degree bound. Equivalently, the coefficient matrix has full row rank. We can select a square minor $\Delta$ that isn't zero.

There's serious geometry in that sentence. Counting more unknown coefficients than equations won't prove that *every* packet of values can be prescribed. The paper gets that stronger statement from estimates on algebraic curves and a degree-bounded interpolation argument. We can use the result here without pretending it's an elementary consequence of linear algebra.

Now clear the denominators in the selected matrix. The result has entries in $\mathbb Z[i]$, and its determinant is a nonzero Gaussian integer $a+bi$. Therefore

$$
|a+bi|=\sqrt{a^2+b^2}\ge1.
$$

Divide back by the clearing factors and we have a lower bound on $|\Delta|$.

Unfortunately, clearing too many denominators would make that bound too weak. You can see the saving we need in

$$
(p/q+u)^\gamma.
$$

Its $u^\beta$ coefficient involves only $q^{\gamma-\beta}$ in the denominator when $0\le\beta\le\gamma$. If we charge it for $q^\gamma$, we've wasted a factor of $q^\beta$. The proof preserves these savings by scaling the rows as well as the columns.

The circle coordinates cost something too. Write $\alpha=U/D$ with $U\in\mathbb Z[i]$ and $D$ a positive integer. A column using the $h$-th power of the exponential coordinate contributes $\alpha^{jh}$, and the clearing identity is

$$
D^{Kh}\alpha^{jh}=U^{jh}D^{(K-j)h}.
$$

For our example, $D=5$. Having modulus one doesn't make a denominator disappear, and deleting these factors would change the determinant we're trying to bound.

For the upper bound, expand near

$$
z_j(t)=ij\vartheta+\log(1+t).
$$

Then $e^{z_j(t)}=\alpha^j(1+t)$ exactly. The approximate additive coordinate differs from the exact one by $ij(p_k/q_k-\vartheta)$, so rotating by $i$ hasn't made the approximation error any larger. The truncated logarithm contributes another error, which we also have to keep. (The logarithm here is local; we aren't treating the principal logarithm of every $\alpha^j$ as $ij\vartheta$.)

Taylor expansion expresses the determinant through functions such as $e^{hz}z^d$. If two expanded rows use the same transverse index and the same Taylor order, that term vanishes. Surviving terms must either use enough higher Taylor orders to become small, or acquire enough powers of the tiny approximation errors to become small. That gives the upper bound on the same $\Delta$.

Getting the bounds to disagree takes a careful choice of weights and dimension. For example, if $w_0$ is the weight of the exponential coordinate, the extra denominator cost is $K\log D/w_0$. The complex analytic radius contributes $\rho K/w_0$, with $\rho$ fixed once the angle is fixed. The parameter construction makes $K/w_0$ small while making the cancellation estimate stronger. Then we choose our approximation denominators, and only after those choices do we let the interpolation height grow. For every $\nu>2$, the upper bound eventually falls below the lower bound.

So the supposed supply of excellent fractions can't exist.

## Back to the angle we wanted

We proved the bound for $\vartheta=2\arctan r$. Dividing by 2 is straightforward, but there's a small factor to account for. Choose $2<\lambda<\nu$. For sufficiently large $q$,

$$
|\vartheta/2-p/q|
=\tfrac12|\vartheta-2p/q|
\ge\tfrac12q^{-\lambda}
\ge q^{-\nu}.
$$

Division by 4 works the same way, which handles $r=1$ through $\arctan1=\pi/4$ and the earlier π bound. Negation handles $r=-1$. This uses the particular rational scalings we need; it doesn't establish invariance under arbitrary algebraic scaling.

The resulting eventual lower bound even permits unreduced fractions. If $\arctan r$ were rational, we could write its exact value with larger and larger denominators and keep getting zero error, contradicting that bound. We now know it's irrational, Dirichlet supplies exponent 2, and the determinant argument excludes every exponent above 2.

For $\arctan(1/2)$, we've gone from the exact point $(3+4i)/5$ to a restriction on fractions with every sufficiently large denominator. More calculator digits wouldn't have settled that question.

*Casper initiated and directed this work. OpenAI coding agents contributed substantially to the mathematics and exposition, building on OpenAI's method and the preceding rational-logarithm work. Formal-checking details and their scope are in the [verification record](../lean/VERIFICATION.md); no external human peer review or exhaustive priority claim is asserted.*
