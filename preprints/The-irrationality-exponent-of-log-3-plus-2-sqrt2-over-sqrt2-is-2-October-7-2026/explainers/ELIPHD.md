# The real quadratic norm argument behind the normalized logarithm theorem

Ryan Matthew Casper's [paper](../paper.pdf), dated 7 October 2026, proves

$$
\mu\!\left(\frac{\log(3+2\sqrt2)}{\sqrt2}\right)=2.
$$

The point of this explainer is to isolate the arithmetic adaptation for a reader comfortable with graduate mathematics but unfamiliar with this interpolation framework. The [manuscript](../build/manuscript.md) gives the full proof and parameter inequalities.

Write $\beta=\sqrt2$, $u=3+2\beta$, and $x=\log(u)/\beta$. The proved quantitative statement is

$$
\forall\nu>2\ \exists Q\in\mathbb Z,\ Q\ge2:\quad
\forall p,q\in\mathbb Z,\ q\ge Q\Longrightarrow
q^{-\nu}\le |x-p/q|.
$$

This includes unreduced fractions, so it proves irrationality as well as the upper bound on the exponent. Dirichlet supplies the lower bound. The threshold is existential; the theorem does not assert effectivity or bad approximability.

## The inherited method and the new obstruction

OpenAI's [work on $\pi$](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026) supplies weighted logarithmic interpolation, a Taylor-collision estimate for determinants, and a parameter scheme reaching every exponent above 2. Casper's preceding [rational-logarithm](../../The-irrationality-exponent-of-positive-rational-logarithms-is-2-October-7-2026/README.md) and [imaginary-quadratic](../../The-irrationality-exponent-of-arctan-sqrt2-over-sqrt2-is-2-October-7-2026/README.md) adaptations supply further interfaces. These are substantial inherited components, not elementary interpolation facts being assumed without proof.

In the imaginary quadratic setting, an integral norm controls the magnitude of a single complex embedding. Here, for $z=a+b\beta\in\mathcal O=\mathbb Z[\beta]$,

$$
N(z)=a^2-2b^2=\sigma_+(z)\sigma_-(z),\qquad
\sigma_\pm(z)=a\pm b\sqrt2.
$$

For $z\ne0$, this yields only a product lower bound. Units immediately show why one factor is insufficient: $\sigma_-(u^n)\to0$ while the norm remains 1. We need analytic control of both conjugates of the same determinant.

The normalization provides

$$
e^{\beta x}=u,\qquad e^{-\beta x}=u^{-1}.
$$

It is built into the proof. No invariance of the irrationality exponent under algebraic irrational scaling is used or follows from the result.

## Fix the minor before applying either norm estimate

Assume approximants $r_k=p_k/q_k$ with error at most $q_k^{-\nu}$ are available at arbitrarily large positive denominators. Choose finitely many with suitably separated logarithmic weights $w_k=\lceil\log q_k\rceil$. Let $G_k(t)$ be the prescribed rational truncations of $\log(1+t)$.

For sign $\varepsilon$, rows $(j,s,a)$ and monomial columns $(h,\gamma)$ give entries

$$
A^\varepsilon_{(j,s,a),(h,\gamma)}=
[t^sv^a]\,(u^{\varepsilon j}(1+t))^h
\prod_k(\varepsilon\beta jr_k+G_k(t)+v_k)^{\gamma_k}.
$$

Weighted degree restricts the columns; a related weighted simplex restricts the rows. Both multiplicative-center sequences are injective. The inherited theorem applies at sufficiently large cofinal heights, giving full row rank for $A^+$. Choose a nonzero square minor containing all rows, and use its exact column set to define $\Delta_H^-$ in $A^-$.

I would check this choice before reading any asymptotic estimate. Two separately selected minors need not be conjugate, even if each satisfies an attractive analytic bound.

Let $T_k$ be the truncation lengths, $L_k=\operatorname{lcm}(1,\ldots,T_k)$, and $E_H=\prod_kL_k^{\lfloor H/w_k\rfloor}$. At this endpoint the base denominator is 1. Clearing columns by $\prod_kq_k^{\gamma_k}$, rows by $\prod_kq_k^{-a_k}$, and entries by $E_H$ gives a matrix over $\mathcal O$. Its entries, when $a\le\gamma$, are

$$
E_Hu^{jh}\binom\gamma a[t^s](1+t)^h
\prod_k(\beta jp_k+q_kG_k(t))^{\gamma_k-a_k}.
$$

The lcm powers clear the rational Taylor coefficients. More precisely, one first constructs the integral polynomial $L_kG_k$ and the resulting order-valued coefficient expression. This avoids treating integrality at the two embeddings as unrelated facts.

For the resulting matrix $B_H$ and a common $C_H>0$,

$$
\sigma_\pm(\det B_H)=C_H\Delta_H^\pm.
$$

Thus $\Delta_H^+\ne0$ implies $\det B_H\ne0$ and

$$
1\le C_H^2|\Delta_H^+\Delta_H^-|.
$$

The negative determinant's nonvanishing follows here. There is no invocation of an automorphism of $\mathbb R$ or $\mathbb C$ taking the positive square root to the negative one; only the two embeddings of the quadratic order are used.

## Preserve the row saving when averaging

Let $M_H$ count rows and let $b_H$ denote their normalized total transverse weight. The arithmetic estimate is

$$
\frac{\log|\Delta_H^+|+\log|\Delta_H^-|}{2M_HH}
\ge -(1-b_H)-E_{\rm ar},\qquad 0\le b_H\le\theta.
$$

The $b_H$ term comes from row denominator factors. A crude clearing bound that discards it would miss the balance needed as $\nu$ approaches 2.

For the analytic estimates, use local comparison points

$$
z_j^\varepsilon(t)=j\varepsilon\beta x+\log(1+t).
$$

The additive displacement is $\varepsilon\beta j(r_k-x)$ plus the truncation tail $G_k(t)-\log(1+t)$. Both signs have identical displacement norms. The logarithm polynomial remains unchanged; changing its sign would produce the wrong conjugate matrix.

A common analytic radius covers both signs. Taylor expansion of the column functions gives determinant cancellation when rows with the same transverse index repeat a Taylor order. The collision estimate handles the case of many low transverse indices; otherwise the approximation errors provide the saving. At each sign, uniformly over the chosen columns,

$$
\frac{\log|\Delta_H^\pm|}{M_HH}
\le E_{\rm an}+o(1)+
\max\{-c_H,-\nu(A(1-\eta)-b_H)\}.
$$

Averaging leaves the right side unchanged. The norm has doubled the arithmetic logarithm, but we also have two full analytic estimates. That's how the degree-two cost disappears without throwing away the row saving.

## Parameter order and scope

The construction first fixes rational parameters with $0<\theta<A<B<1$ and a positive approximation margin

$$
g=\nu(A(1-\eta)-\theta)-(1-\theta)>0.
$$

Next come the truncation scale, the number of approximants, and the remaining geometric parameters. Only then are the good fractions chosen, with large separated weights paying the small residual costs. Finally $H$ tends to infinity along the cofinal sequence. This order leaves interpolation thresholds free to depend on the fixed centers.

The choices ensure $E_{\rm ar}+E_{\rm an}<g$ and an eventual collision saving larger than the competing arithmetic term. Both alternatives in the maximum contradict the lower bound. The extra factor $\sqrt2$ in the approximation errors contributes an explicit small cost; it isn't silently absorbed into a constant independent of the selected weights.

The formal generic statement accepts compatible period data in $\mathbb Q(\sqrt2)$; the endpoint verifies them for $u=3+2\sqrt2$. It does not establish a theorem for all real quadratic fields or for the bare logarithm.

For historical context, [Bashmakova and Zolotukhina's 2017 family](https://www.mathnet.ru/eng/cheb531) specializes at $d=2$ to $2x$, so comparison is legitimate by rational scaling. [Polyanskii](https://arxiv.org/abs/1501.06752) treats related quadratic families. The manuscript records the limits of the source search rather than identifying a strongest previous bound for $x$.

To inspect the endpoint directly, see [RealNorm/Main.lean](../lean/RealNorm/Main.lean), especially the fully expanded eventual bound, and the [verification record](../lean/VERIFICATION.md). For the mathematical dependency chain, start with the common cleared matrix and then check that the two analytic estimates retain exactly its selected columns.

*Casper initiated and directed the investigation. OpenAI coding agents contributed substantially to the mathematical adaptation, Lean formalization, verification tooling, and exposition. The construction builds on OpenAI's published manuscript and released library, Mathlib, and the preceding adaptations credited above. Formal verification concerns the stated propositions and foundational axioms; it is not external human peer review.*
