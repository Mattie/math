# Targeted prior-art comparison

M. Yu. Luchin and V. Kh. Salikhov, “Approximating ln 2 by numbers in the field
Q(sqrt 2),” Izvestiya: Mathematics 82:3 (2018), 549–577, Theorem 1 on page 549,
states that for each $s>7.98101$,

$$
\left|\log2-\frac{p_1\sqrt2+p_2}{p_3\sqrt2+p_4}\right|>P^{-s},
$$

for integer coefficients with $(p_3,p_4)\ne(0,0)$ and sufficiently large
$P=\max_i|p_i|>P_0(s)$. [Publisher-hosted English text](https://www.mathnet.ru/php/getFT.phtml?jrnid=im&option_lang=eng&paperid=8518&what=fullteng).

For $x=\log2+\sqrt2$, substitute $(p_1,p_2,p_3,p_4)=(-q,p,0,q)$;
the left side is $|x-p/q|$. For $y=\sqrt2\log2$, substitute $(0,p,q,0)$;
the left side is $|y-p/q|/\sqrt2$. In both cases $P=\max(|p|,q)$.
For approximations within distance one of the fixed target $z$, we have
$q\le P\le (|z|+1)q$. Choosing $7.98101<s<\nu$ absorbs the fixed constant
into $q^{\nu-s}$ for sufficiently large $q$. Approximations at distance at
least one already satisfy the eventual lower bound. Hence both irrationality
exponents are at most 7.98101. There is no factor-of-two loss: the coefficient
height here is of order $q$, not $q^2$.

The package's bound of four improves this consequence of that theorem. This
targeted comparison is not an exhaustive search for later or stronger results,
and it does not establish priority. It makes no corresponding best-known-bound
claim for the shifted quadratic period.
