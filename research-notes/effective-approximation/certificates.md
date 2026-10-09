# Explicit integer-linear-form certificates

Ordinary mathematical arguments; no Lean theorem or pi-specific input is asserted. See the [overview](README.md) for authorship, scope, and AI disclosure. No novelty claim is made for these formulations. All displayed prefactors and starting indices must be supplied numerically with proofs. Limits without a certified modulus do not meet this interface.

## 1. A bounded-window certificate, valid at every denominator

Let $\alpha$ be real and $a,b$ be positive integers. Supply rational $E,H>0$, $R,S>1$, integers $n_0,h\ge0$, and integer pairs $(u_n,v_n)$ for every $n\ge n_0$, satisfying

$$|u_n|\le HR^n,\qquad |u_n\alpha-v_n|\le ES^{-n}.$$

For each $n\ge n_0$, assume the pairs with indices in $[n,n+h]$ span a two-dimensional rational vector space. Equivalently, two of these pairs have nonzero determinant. Require

$$R^b\le S^a.$$

Choose rational $M\ge1$ with $M^b\ge(2E)^a$, and set

$$K=\max\{R^{n_0+h},R^{h+1}M\},\qquad c=\frac1{2HK}.$$

Then, for **every** integer $p$ and integer $q\ge1$,

$$\left|\alpha-\frac pq\right|\ge c q^{-(1+a/b)}.\tag{1}$$

**Proof.** Choose

$$n=\max\{n_0,\lceil\log_S(2Eq)\rceil\}.$$

For every $i\in[n,n+h]$, $q|u_i\alpha-v_i|\le1/2$. The nonzero determinant ensures that at least one $u_i p-v_i q$ is a nonzero integer: if two independent pairs both annihilated $(p,-q)$, that vector would be zero, contradicting $q\ge1$. Consequently

$$1\le|u_i p-v_i q|\le |u_i|q|\alpha-p/q|+\frac12.$$

If $n=n_0$, then $|u_i|\le HR^{n_0+h}\le HKq^{a/b}$. Otherwise $n>n_0\ge0$, so $2Eq>1$, and

$$R^i\le R^{h+1}(2Eq)^{\log R/\log S}
\le R^{h+1}(2Eq)^{a/b}\le R^{h+1}Mq^{a/b}.$$

The same bound follows in this case. Substitution proves (1). In particular, the selected $u_i$ cannot be zero: otherwise the preceding integer inequality would read $1\le1/2$.

At $a=7,b=5$, the rate test is $R^5\le S^7$. Its adjacent-determinant version is $h=1$. The maximum in $K$ covers smaller denominators as well, without a finite pi computation. A late starting index only worsens the explicit constant when uniform family estimates are known from that index onward.

No logarithm needs numerical evaluation to implement the index choice. Repeated multiplication by rational $S$ finds the first integer $n\ge n_0$ with $S^n\ge2Eq$; termination follows from $S>1$. Rational $M$ can likewise be found by integer enumeration and exact power comparisons. Replace $c$ by $\min(1,c)$ when an application requires a constant at most one.

## 2. An alternative to bounded-window determinants

This adapts Hata's index-selection mechanism to explicit rational data. The original asymptotic one-number assertion is [Hata, Remark 2.1](https://matwbn.icm.edu.pl/ksiazki/aa/aa63/aa6344.pdf), pp. 339–340. Our rational certificate is as follows.

Let $a,b$ be positive integers and $n_0\ge0$ an integer. Assume $\alpha$ is an irrational real number, supply rational $E,H,J>0$, rational $1<r\le R$ and $S>1$, and suppose that, for all $n\ge n_0$,

$$Jr^n\le |u_n|\le HR^n,\qquad |u_n\alpha-v_n|\le ES^{-n},\qquad u_n,v_n\in\mathbb Z.$$

Require $R^{a+b}\le(rS)^a$. Choose $M\ge1$ as above, put

$$c_1=\frac1{2H\max\{R^{n_0},RM\}},$$

and choose rational $c_2>0$ with

$$c_2^b(2HR)^{a+b}E^a\le J^a.$$

Then (1) holds with $c=\min(c_1,c_2)$. No adjacent-determinant assumption is needed.

**Proof.** Put $\delta=|q\alpha-p|>0$ and choose $n$ as before. If $u_np-v_nq\ne0$, part 1's height argument gives $\delta\ge c_1q^{-a/b}$; its rate inequality follows from $r\le R$. Otherwise some later index $m$ has nonzero integer determinant, since persistent coincidence would force $\delta\le(qE/J)(rS)^{-k}\to0$. Take the first such $m$. With $T=rS$,

$$\delta\le(qE/J)T^{-(m-1)},\qquad\delta\ge(2HR^m)^{-1}.$$

Because $qE/(J\delta)\ge T^{m-1}\ge1$ and $\log R/\log T\le a/(a+b)$,

$$R^m\le R\left(\frac{qE}{J\delta}\right)^{a/(a+b)}.$$

Combine and raise to power $a+b$:

$$\delta^b\ge(2HR)^{-(a+b)}(J/E)^a q^{-a}\ge c_2^bq^{-a}.$$

Division by $q$ proves the assertion. This derivation does not require computing $m$.

For $12/5$, the rate test becomes $R^{12}\le(rS)^7$. The lower coefficient estimate is essential; merely having infinitely many noncoincident indices supplies neither lemma.

## 3. A non-pi check with actual integer forms

Write $(3+2\sqrt2)^n=v_n+u_n\sqrt2$. For $n\ge1$, these are positive integers,

$$|u_n\sqrt2-v_n|=(3-2\sqrt2)^n\le5^{-n},\qquad\tfrac14 5^n\le u_n\le6^n.$$

For the lower bound, $3+2\sqrt2>5$, its inverse is below 1, and $2\sqrt2<3$, so $u_n>(5^n-1)/3\ge5^n/4$. The upper bound is immediate from $3+2\sqrt2<6$. The recurrence $(v,u)\mapsto(3v+4u,2v+3u)$ preserves $v^2-2u^2=1$, and $u_nv_{n+1}-u_{n+1}v_n=-2$.

Thus part 1 applies with $n_0=h=1$, $E=H=1$, $R=6,S=5$, $M=3$ and yields $c=1/216$ at $12/5$. Part 2 applies with $J=1/4,r=5$ and permits $c_2=1/27648$. The exact checks $6^5\le5^7$, $6^{12}\le25^7$, $3^5\ge2^7$, and $c_2^5 12^{12}\le4^{-7}$ can be verified by integer arithmetic after clearing denominators. These intentionally weak constants verify that the interfaces have concrete instances. They are **not** pi constants.

## 4. What a family must actually provide

An integral or holonomic recurrence needs an exact identification with $u_n\pi-v_n$, integer coefficients **after** all denominator costs, uniform absolute error bounds, uniform coefficient bounds, a numerical starting index, and one of the two noncoincidence mechanisms above. Fixed signs are useful for lower bounds, but are not assumed in part 1. Oscillatory remainders are allowed because the error estimate is absolute.

Polynomial factors in an asymptotic expression must be absorbed with explicit slack and a computed threshold. An equality of limiting rates at $7/5$ does not permit arbitrary slack; a strict favorable margin is therefore the practical acceptance criterion. Sampling determinants, estimating gcd growth, or proving a recurrence identity alone does not establish any missing all-index estimate.
