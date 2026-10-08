# How good can a fraction be?

Here's our angle, measured in radians and rounded to 20 decimal places:

$$
\arctan(1/2) \approx 0.46364760900080611621.
$$

It's the angle in a right triangle whose opposite side has length 1 and adjacent side has length 2. The name $\arctan(1/2)$ means “the angle whose tangent is $1/2$.”

Here are a few fractions that approximate its value:

| Fraction | Decimal value (rounded) | Error (approximately) |
|---|---:|---:|
| $58/125$ | 0.464000000000 | 0.000352390999 |
| $51/110$ | 0.463636363636 | 0.000011245364 |
| $338/729$ | 0.463648834019 | 0.000001225018 |
| $389/839$ | 0.463647199046 | 0.000000409954 |

These are close matches, not exact ones. Notice that $51/110$ does better than $58/125$ even though its denominator is smaller. Can we keep finding fractions that get unusually close without needing enormous denominators?

That's the question behind Ryan Matthew Casper's [*The irrationality exponent of nonzero rational arctangents is 2*](../paper.pdf), dated 7 October 2026. There's a [full manuscript](../build/manuscript.md), but let's work out what the result says before getting into its proof.

We're using radians throughout. If we picked $\arctan1$ as our example, we'd get $\pi/4$ radians or 45 degrees. The angle is the same, but 45 is already an exact fraction, $45/1$. We need to agree on units before asking how well fractions approximate its numerical value.

## Getting closer is easy. How much denominator did it take?

You can approximate any real number by rounding to more decimal places. Six places gives you a fraction with denominator one million. Ten places gives you a denominator of ten billion. The error gets smaller, but those denominators get large pretty quickly.

So let's compare the error with the denominator itself. If a fraction has denominator $q=1000$, then

$$
\frac1{q^2}=0.000001,\qquad
\frac1{q^3}=0.000000001.
$$

An error below the second number is a thousand times smaller. Asking for an error below $1/q^3$ is much more demanding, and as $q$ grows it gets more demanding still.

A classical result called Dirichlet's approximation theorem says every irrational number has infinitely many reduced fractions with positive error below $1/q^2$. “Reduced” means we've canceled common factors, so $1/2$ and $500/1000$ count as the same fraction.

The paper's result is that, for the arctangent of any nonzero rational number, 2 is exactly the dividing point:

- There are infinitely many fractions with error below $1/q^2$.
- Pick any fixed exponent above 2, even 2.001, and only finitely many reduced fractions will have error below that stricter bound.

That's what *irrationality exponent 2* means here. The paper also proves that these radian values are irrational. It covers $\arctan(1/2)$, $\arctan3$, and $\arctan(-2/7)$, for example. Zero has to be excluded because $\arctan0=0$.

There can still be a few remarkably good fractions. The theorem says that each stricter requirement eventually stops being attainable; it doesn't give us a handy denominator where that happens. And the exponent-2 result doesn't guarantee an error of at least $c/q^2$ for some fixed positive $c$. That's a stronger claim. (Each time we change 2.001 to something closer to 2, the eventual cutoff is allowed to move.)

## Why look at a doubled angle?

The proof grew out of OpenAI's [earlier paper about π](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026). That paper supplied a method for turning “suppose we had too many excellent fractions” into a contradiction. It constructs a particular nonzero number and then shows that those excellent fractions would force the number to be smaller than arithmetic allows.

Our preceding [paper on logarithms](../../The-irrationality-exponent-of-positive-rational-logarithms-is-2-October-7-2026/README.md) extended that method to numbers such as $\ln2$. The relation $e^{\ln2}=2$ gives an exact rational number to work with, and taking whole-number multiples of the exponent gives $4,8,16,\ldots$.

We'd like something similarly useful for our angle. The double-angle formulas provide it. If $x=\arctan(1/2)$, then

$$
\cos(2x)=\frac35,\qquad \sin(2x)=\frac45.
$$

So doubling the angle lands exactly at the point $(3/5,4/5)$ on the unit circle. You can check that point belongs to the circle without knowing any digits of $x$: $(3/5)^2+(4/5)^2=1$.

The angle is awkward to write exactly as a decimal, but the point is easy to calculate with. This works for every rational input $r$:

$$
\cos(2\arctan r)=\frac{1-r^2}{1+r^2},\qquad
\sin(2\arctan r)=\frac{2r}{1+r^2}.
$$

Fractions in, fractions out. The proof uses complex numbers to keep track of points at successive multiples of the doubled angle, while preserving those rational coordinates.

The points usually don't repeat. The paper proves that the repeating cases in this family come from $r=0,1,-1$. We leave out zero, and the other two are familiar: $\arctan1=\pi/4$ and $\arctan(-1)=-\pi/4$. The π result takes care of those.

## Where the contradiction comes from

A nonzero integer has absolute value at least 1. If a calculation tells us that the same integer is nonzero and has absolute value below 1, something in the assumptions must be wrong.

The proof uses a large determinant to arrange this kind of conflict. A determinant is a number calculated from a square array of entries. For a two-by-two array

$$
\begin{pmatrix}a&b\\c&d\end{pmatrix},
$$

the determinant is $ad-bc$. Integer entries give an integer answer, so if the answer isn't zero, it can't be arbitrarily tiny.

The calculation first works with twice our angle. Suppose that doubled angle had fractions meeting some fixed exponent above 2 at arbitrarily large denominators. The proof selects finitely many of them and builds a matrix from polynomial coefficients near carefully chosen points. Those rational circle points help make the entries exact.

We need the determinant to be nonzero. That's a difficult part of the proof. It uses *interpolation*, which means finding a polynomial with prescribed values or derivatives. You've seen a small version if you've matched a function's value and slope with a tangent line, or matched several derivatives with a Taylor polynomial. Here there are many points and several variables, with limits on the allowed degrees. The theorem that makes all of this work requires algebraic geometry, well beyond what we'll derive here.

Once that theorem gives us a nonzero determinant, there are two ways to estimate it. Clearing denominators gives a lower bound on its size. Taylor series, using the supposed excellent fractions, give an upper bound. In the expanded determinant, repeated rows cancel, and the remaining terms involve higher Taylor orders or enough factors of the small approximation errors. With the right choices, their total becomes smaller than the lower bound. That can't happen to the same number.

There's an extra complex-number detail: the cleared determinant has integer real and imaginary parts. Its magnitude is $\sqrt{a^2+b^2}$ for integers $a,b$, so the same “nonzero means at least 1” observation works.

Getting useful bounds takes some care. If we multiply a fraction by a huge denominator to make an integer, then divide back, the lower bound may be too small to help. For example,

$$
(p/q+u)^2=p^2/q^2+(2p/q)u+u^2.
$$

The coefficient of $u$ only needs a factor of $q$ to clear its denominator. Using $q^2$ would work, but would waste a factor of $q$. The proof keeps that sort of saving in its matrix rather than clearing every entry with an unnecessarily large factor.

It also keeps track of the denominators in the circle coordinates. Being on the unit circle doesn't remove the 5 from $3/5$ and $4/5$. The proof has to accommodate those costs while making the Taylor estimate strong enough. This is considerably more work than the small determinant example, but you can see what all that work has to accomplish.

Finally, we return from twice the angle to the angle itself. If $p/q$ is close to $x/2$, then $2p/q$ is close to $x$, with twice the error. A small amount of room between two exponents above 2 absorbs that fixed factor once $q$ is large. Dividing by 4 handles the $\pi/4$ case in the same way. Multiplying by an arbitrary algebraic number would require its own argument.

The proof's eventual positive lower bound applies even to unreduced fractions. That rules out an exact rational answer: an exact fraction could be rewritten with ever larger denominators and still have zero error. Dirichlet's theorem then supplies infinitely many exponent-2 approximations, and the contradiction above rules out an infinite supply at any larger exponent.

Our fraction $51/110$ is still a good approximation. You can find others, and a calculator is useful for exploring them. What a finite list can't settle is the claim about every sufficiently large denominator. That's the part the proof supplies.

*Casper directed this work, with substantial help from OpenAI coding agents in the mathematics and writing. It builds on OpenAI's method and the preceding logarithm extension. The [verification record](../lean/VERIFICATION.md) gives the formal-checking details; no external human peer review or exhaustive priority claim is asserted.*
