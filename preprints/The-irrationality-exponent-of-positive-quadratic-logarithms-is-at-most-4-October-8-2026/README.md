# The irrationality exponent of positive quadratic logarithms is at most 4

**Ryan Matthew Casper · October 8, 2026**

[Read the paper](paper.pdf), with [editable manuscript](build/manuscript.md) and [LaTeX source](build/main.tex).

For every positive real quadratic algebraic number $a\ne1$, the logarithm $\log a$ has irrationality exponent at most four. The result allows nonintegral inputs and negative conjugates. It gives an eventual bound for each exponent strictly above four; it does not compute the threshold or establish equality with four.

The [Lean endpoint](lean/AlgebraicLog/Main.lean) and examples accompany the paper. [Verification and reproduction](VERIFY.md) separates native compilation, exported-proof checks, automated review, and remaining trust limits. The overlay fetches the pinned rational-logarithm project rather than duplicating its 924 source files.

## AI use and attribution

The author initiated and directed an investigation of extending OpenAI’s irrationality-exponent method to logarithms of positive quadratic algebraic numbers. OpenAI coding agents contributed substantially to developing the candidate argument, producing the Lean formalization, and conducting automated adversarial reviews. The construction builds on OpenAI’s published manuscript and released Lean library, the preceding rational-logarithm extension, and Mathlib. Automated checking and model review are distinct from independent human mathematical review.

See [citation metadata](CITATION.cff), [license scope](LICENSES.md), and [notices](NOTICE).

[Verification status and retained-export downloads](VERIFY.md#verification-and-distribution-update).
