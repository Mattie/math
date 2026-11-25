# The irrationality exponent of π² is less than 4.589897

This proof supplement establishes an unrestricted bound for rational approximation to the square of the usual real number π. In lowest terms, a rational number has the positive denominator `q.den`.

| Lean declaration in `PrimeNumerator.WindowFinal` | Statement |
| --- | --- |
| `rational_upper_bound` | The irrationality measure of π² is at most 821200073639400000000 / 178914706731744129841. |
| `irrationality_measure_pi_sq` | The irrationality measure of π² is strictly less than 4.589897. |
| `finite_good_ratios` | Only finitely many rational numbers q satisfy abs(π² − q) < q.den^(−4.589897). |

The declarations are in [WindowFinal.lean](src/WindowFinal.lean). The definition of irrationality measure is the infimum of upper bounds expressed by finiteness of exceptionally good rational approximations.

The companion [WindowCatalogue.lean](src/WindowCatalogue.lean) expresses the bound using the supremum of Mathlib's `LiouvilleWith` approximation exponents. It uses the expanded definition in [Formal Conjectures, Constant 7a](https://github.com/google-deepmind/formal-conjectures/blob/2207c54d0dbe960de591d280f997b195bf3f6e28/FormalConjectures/OptimizationConstants/7a.lean), evaluated at π².

## Reproduce the proof

Use Linux or WSL with Bash, Git, Python 3, GNU coreutils, and a working Lean toolchain manager (Elan). The pinned project selects Lean 4.35.0-rc4 and Mathlib commit `1f414401f69059aa7eead47b53ee40bd38455eeb`. Allow internet access for the named repositories, Lean toolchain, and Mathlib cache, and sufficient local disk space for these dependencies.

```sh
bash reproduce.sh
```

An existing clean upstream checkout at the specified commit can be passed as the first argument. The script writes the generated sources, build products, axiom audit, and transcript in the temporary working directory printed at startup. It checks the manifest before building and requires the three final declarations to report exactly `propext`, `Classical.choice`, and `Quot.sound`. For a short independent check of the numerical inequality, run `python3 check_rate.py`; it rounds down six million positive rational terms using integer arithmetic.

## Proof and dependencies

Leibtag, Barkan, Kalisch, Weinbaum, Shalyt, and Kaminer constructed the integer approximations to ζ(2) and supplied their height, error, and independence estimates. The additional prime divisors in this paper occur in positive integer translates of six original intervals. The build reconstructs the adapted kernel proof passages from pinned source, proves simultaneous divisibility of the published pair, and sums disjoint windows over one million fixed periods. It then applies the irrationality criterion to the reduced pair and uses π² = 6ζ(2). [New Directions in Irrationality](https://arxiv.org/abs/2610.27799) · [Pinned trajectory proof](https://github.com/RamanujanMachine/zeta2_four_trajectory_matrices/tree/a0e8ac417cddc6ffa88e43cfd68d2b58ea339517)

The trajectory formalization declares the prime number theorem as an axiom. The replay substitutes a theorem with the same statement and rebuilds its downstream dependents. Its proof adapts a hash-pinned selection of the Apache-2.0 PrimeNumberTheoremAnd sources, retaining attribution and the upstream license in the generated proof directory. [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/127b50e33f6033e2147921167a117af96d9ba4ea)
