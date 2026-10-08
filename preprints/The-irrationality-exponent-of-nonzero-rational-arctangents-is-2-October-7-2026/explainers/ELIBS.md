# How close can a fraction get to an angle?

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

Rounding the angle to $0.464$ gives $58/125$. But $51/110$ gets quite a bit closer with a smaller denominator. So there's more to finding good fractions than keeping another decimal place. How much accuracy can we get for the denominator we're using?

The displayed decimals are rounded; none of these fractions equals the irrational value exactly.

Ryan Matthew Casper's [*The irrationality exponent of nonzero rational arctangents is 2*](../paper.pdf), dated 7 October 2026, asks how far this can go. The [manuscript](../build/manuscript.md) gives the full proof; we'll follow the main idea with the angle above as our example.

## What counts as a good fraction?

We need to compare the error with the denominator. An error of one millionth is impressive with a small denominator, but you can get that accuracy for any real number simply by rounding to six decimal places.

A useful benchmark is $1/q^2$, where $q$ is the denominator in lowest terms. Our fraction $51/110$ beats it: its error is about $0.00001125$, while $1/110^2$ is about $0.00008264$. A theorem of Dirichlet says that every irrational number has infinitely many reduced fractions with error below $1/q^2$. You don't have to be an arctangent to get those.

Now ask for errors below $1/q^{2.01}$ instead. That's a little stricter at first and increasingly stricter as $q$ grows. Asking for $1/q^3$ is stricter still. The *irrationality exponent* records how far we can raise that power while still succeeding infinitely often: it's the supremum of the exponents for which infinitely many reduced fractions have positive error below $1/q^\nu$.

The paper proves that $\arctan r$ is irrational and has exponent exactly 2 for every nonzero rational $r$. You can use $r=1/2$, $r=3$, or $r=-2/7$. Zero is left out because its arctangent is exactly zero.

For each fixed $\varepsilon>0$, the conclusion says that

$$
|\arctan r-p/q|\ge\frac1{q^{2+\varepsilon}}
$$

once $q$ is sufficiently large, for every numerator $p$. This still leaves room for some very good fractions before that threshold. It also doesn't give a fixed positive $c$ such that every error is at least $c/q^2$: as we make $\varepsilon$ smaller, the threshold can change. There's no permission to put $\varepsilon=0$ in that inequality.

And these are radian values. For $\arctan1$, we're approximating $\pi/4$, not the number 45. (Switching the calculator to degrees would make that particular approximation problem awfully short.)

## How did π lead to a point on a circle?

OpenAI's [paper on the irrationality exponent of π](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026) supplied the method behind this proof. It uses polynomial interpolation to construct a nonzero determinant, then compares an arithmetic lower bound with an analytic upper bound. Fractions that are too good would force those bounds to disagree.

Our preceding [rational-logarithm paper](../../The-irrationality-exponent-of-positive-rational-logarithms-is-2-October-7-2026/README.md) extended the method to numbers such as $\log2$. There, exponentiation gives exact rational numbers: $e^{\log2}=2$, $e^{2\log2}=4$, and so on. Those rational coordinates are useful when we need to clear denominators later.

For arctangents, we can get rational coordinates by doubling the angle. Let $x=\arctan(1/2)$. Since $\tan x=1/2$, the double-angle formulas give

$$
\cos(2x)=\frac{1-(1/2)^2}{1+(1/2)^2}=\frac35,\qquad
\sin(2x)=\frac{2(1/2)}{1+(1/2)^2}=\frac45.
$$

There's our familiar 3–4–5 triangle, scaled down to the unit circle. The angle's decimal expansion is inconvenient, but this point is exact.

We can write the point as the complex number $\alpha=3/5+(4/5)i$. Multiplying complex numbers adds their angles, so $\alpha^j$ represents the angle $2jx$. Every such power still has rational real and imaginary parts. For a general rational input,

$$
e^{2i\arctan r}=\frac{1-r^2}{1+r^2}+i\frac{2r}{1+r^2},
$$

and the same arithmetic is available.

Most of these powers never repeat. The paper proves that rational-coordinate points on the unit circle can have repeating powers only at $1,-1,i,-i$. Among our finite rational inputs, that leaves $r=0,1,-1$. We already excluded zero, and the other two angles are $\pm\pi/4$, so the earlier π result will handle them.

## The determinant has to be nonzero, and then it has to be too small

If you've met determinants, here's the arithmetic fact we'll use. An integer matrix has an integer determinant. If that determinant is nonzero, its absolute value is at least 1. For a two-by-two matrix, this is just the observation that the integer $ad-bc$ can't sit strictly between 0 and 1.

With fractions in the entries, we can clear denominators to get a related lower bound. With rational complex coordinates, the cleared determinant becomes $a+bi$ for integers $a,b$, and a nonzero one still has magnitude at least 1 because $a^2+b^2\ge1$.

The hard part is constructing a determinant that is both nonzero and small enough to contradict that bound.

Suppose fractions approximate $2\arctan r$ better than $1/q^\nu$ for some fixed $\nu>2$, with arbitrarily large denominators. Select finitely many of them and use them, together with the circle points $\alpha^j$, to specify interpolation centers. The matrix records Taylor coefficients of polynomials near those centers.

Interpolation may be familiar from finding a polynomial through several points. Here we want to prescribe derivatives as well, in several variables, while keeping the polynomial's degrees under control. A substantial theorem guarantees enough independence among these conditions to select a nonzero determinant. Its proof uses algebraic geometry; it's the part we won't derive here. Simply having lots of coefficients available doesn't guarantee that every set of requested values can be attained.

Once we have the determinant, exact arithmetic gives the lower bound. Taylor expansion gives the upper bound. The proposed fractions make certain differences between the approximate and exact centers tiny. In the expansion, terms with repeated rows vanish, while the surviving terms must pay through higher Taylor orders or through enough factors of those tiny errors. With the right parameters, the entire determinant comes out too small.

There is some surprisingly consequential denominator accounting along the way. Consider

$$
(p/q+u)^3=(p/q)^3+3(p/q)^2u+3(p/q)u^2+u^3.
$$

The $u^2$ coefficient only needs one power of $q$ to clear its denominator. If we multiply it by $q^3$ anyway, we get an integer, but we've weakened the bound we'll obtain when we divide back. The proof preserves this saving across the rows of its matrix.

We also have to keep the circle factors themselves. Although $|\alpha|=1$, its coordinates have denominator 5 in our example. Powers of $\alpha$ contribute real denominator costs, and they affect the determinant. We can't delete them just because they don't change the length of an individual complex number.

The proof chooses weights and a number of variables that make these costs small enough, chooses suitable approximation denominators, and then increases the matrix's interpolation height. The two estimates eventually disagree for every exponent above 2. That rules out the assumed endless supply of exceptionally accurate fractions.

There's one last step: the construction used twice our angle. If $x=2\arctan r$, then

$$
|x/2-p/q|=\tfrac12|x-2p/q|.
$$

We start with a bound at an exponent between 2 and the exponent we want; for large $q$, that extra room absorbs the factor $1/2$. Division by 4 works the same way for $\pi/4$, and changing the sign handles $-\pi/4$. This is an argument for the rational scalings used here. We haven't proved a corresponding rule for arbitrary algebraic multipliers.

The eventual lower bound permits unreduced fractions too. An exact rational value could be rewritten with endlessly larger denominators and zero error, so the bound proves irrationality. Dirichlet then gives exponent 2 from below, and our contradiction excludes everything above it.

You can keep looking for good fractions such as $51/110$. The theorem leaves plenty of them to find. What it rules out is an infinite supply meeting any one fixed exponent above 2, however small the increase.

*Casper initiated and directed the work, with substantial contributions from OpenAI coding agents to the mathematics and writing. The paper credits OpenAI's method and the preceding rational-logarithm extension. See the [verification record](../lean/VERIFICATION.md) for formal-checking details; the work does not claim external human peer review or exhaustive priority.*
