# What the investigation established

This is a record of a bounded investigation, with literature inspected on October 8, 2026. It separates reusable arguments from unresolved requirements. See the [overview](README.md) for authorship, scope, and AI disclosure.

## Finitely many exceptions is not a numerical threshold

A proof that only finitely many fractions violate an approximation inequality need not identify the largest exceptional denominator. In the inspected OpenAI construction, the contradiction uses a sufficiently separated tuple of exceptional approximations. Excluding such tuples establishes finiteness, but does not locate a last isolated exception.

Making an auxiliary interpolation degree explicit for a supplied tuple does not resolve this problem: the tuple and a bound on its location are different inputs. A finite continued-fraction computation also leaves the unexamined denominators uncontrolled.

The inspected [OpenAI introduction](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/build/main.tex) and [conclusion](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/build/sections/conclusion.tex) retain this effectivity limitation. This observation concerns the released argument; it is not a proof that an effective refinement is impossible.

## What an explicit linear-form family would supply

Write $L_n=u_n\alpha-v_n$ with integer coefficients. Suppose the coefficient and error estimates have approximate exponential rates

$$
|u_n|\lesssim e^{\sigma n},\qquad |L_n|\lesssim e^{-\tau n}.
$$

With the uniform estimates and independence required in [the first certificate lemma](certificates.md), the corresponding approximation exponent is $1+\sigma/\tau$. For the target $12/5$, the desired ratio is at most $7/5$; for any exponent below $5/2$, it must be below $3/2$.

Limiting rates alone are insufficient. A numerical certificate needs explicit prefactors, a numerical starting index, integer coefficients after denominator clearing, and control of coincidences with the fraction being tested. A strict rate margin makes it possible to absorb polynomial factors; equality of limiting rates does not automatically do so.

| Inspected construction | Reported or derived exponent | Relevance |
| --- | ---: | --- |
| Hata's simultaneous logarithmic integral | 8.0161 | Provides a useful way to handle coincident approximations; the rate is too weak here. |
| Zeilberger–Zudilin integral and recurrence | About 7.103205334137 | Concrete family suitable for exact diagnostics, but far from the required rate. |
| Bai's two-parameter refinement | 7.101862832357 | Strongest inspected numerical exponent; still too weak for this application. |
| Calegari–Dimitrov–Tang arithmetic holonomy example | 15.086 | An alternative quantitative mechanism, not a suitable input at the displayed rate. |

Sources: [Hata, Theorem 1.1 and Remark 2.1](https://matwbn.icm.edu.pl/ksiazki/aa/aa63/aa6344.pdf), [Zeilberger–Zudilin, Part II](https://arxiv.org/html/1912.06345v2), [Bai, §§2–5](https://arxiv.org/html/2609.11276v2), and [Calegari–Dimitrov–Tang, §3.3](https://math.berkeley.edu/~ytang/ICM.pdf). These are assessments of the cited texts, not independent verifications of their theorems. A displayed exponent is also not the same as a supplied global numerical constant.

## How much arithmetic improvement would be needed?

For Bai's construction, using its normalization per $5570n$, the inspected logarithmic rates are approximately

$$
\sigma=3.871937805377,\qquad
\tau=0.634550122111.
$$

Suppose a proved additional common divisor saved exponential rate $d$. Dividing both integer coefficients by it would change the ratio to

$$
\frac{\sigma-d}{\tau+d}.
$$

Reaching $7/5$ would therefore require

$$
d\ge\frac{5\sigma-7\tau}{12}\approx1.243153181009.
$$

Even the hypothetical saving of the entire identified clearing cost, approximately $0.539993819199$ in this same normalization, leaves an exponent about $3.836798070289$. Thus that particular improvement alone would not suffice. These calculations do not exclude additional divisibility or a different construction; they quantify the scale of improvement required. The input enclosures are in [Bai, equations (5.18)–(5.21)](https://arxiv.org/html/2609.11276v2).

## What finite experiments can tell us

In the investigation, exact recurrence calculations for the Zeilberger–Zudilin family covered indices 0 through 240. The calculation cleared denominators, removed each pair's full integer gcd, and used rational enclosures of π to bound the errors. All 240 tested adjacent determinants were nonzero. The first six terms were also compared with an independent partial-fraction calculation of the integral.

Those checks did not reveal a useful persistent improvement. They establish neither all-index independence nor an asymptotic gcd rate. An unusually good early term can be misleading: a useful certificate requires coverage at every denominator scale.

This paragraph reports the scope of exploratory computations; this notes-only collection does not ship their implementation or constitute a reproducible computational proof package. None of the certificate proofs depends on those finite results.

## Combining good approximations has a cost

Suppose two families approximate constants $\alpha_1,\alpha_2$. The natural construction for their sum multiplies denominators and produces error terms $u_2L_1+u_1L_2$. With ordinary independent exponential estimates, both terms would decay only if

$$
\tau_1t_1>\sigma_2t_2,\qquad
\tau_2t_2>\sigma_1t_1,
$$

where $t_1,t_2>0$ describe the relative indices. When both $\tau_i<\sigma_i$, these inequalities cannot hold together: multiplying them gives a contradiction.

This is a limitation of that direct estimate, not an impossibility theorem for combinations. Shared denominators or proved cancellation could change the calculation. It explains why strong separate arctangent results do not automatically produce an effective π bound through a Machin identity.
