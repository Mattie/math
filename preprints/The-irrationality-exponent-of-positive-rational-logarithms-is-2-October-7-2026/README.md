# [The irrationality exponent of positive rational logarithms is 2](paper.pdf)

**Author:** Ryan Matthew Casper

**Date:** October 7, 2026

## Citation

```bibtex
@misc{Casper2026RationalLogarithms,
  author = {Casper, Ryan Matthew},
  title = {The irrationality exponent of positive rational logarithms is 2},
  howpublished = {Preprint with Lean formalization},
  year = {2026},
  month = {oct}
}
```

For a reproducible citation, include the published repository URL and exact
commit or release tag. [CITATION.cff](CITATION.cff) provides machine-readable
author and title metadata.

The theorem concerns each natural logarithm of a positive rational number
other than 1, including the individual cases log 2 and log 3. It does not
assert an exponent for their quotient.

- [TeX source](build/main.tex).
- [Lean proof](lean/Logarithm/Main.lean) and [verification report](lean/VERIFICATION.md).
- [Reproduction](VERIFY.md) and [statement validation](review/blind-statement/CertifiedBridge.lean).
- [License scope](LICENSES.md).

The author initiated and directed an investigation of extending OpenAI’s irrationality-exponent method to logarithms of positive rational numbers. OpenAI coding agents contributed substantially to developing the candidate argument, producing the Lean formalization, and conducting automated adversarial reviews. The construction builds on OpenAI’s published manuscript and released Lean library.

The internal reviews are automated; external human peer review and a complete
priority review have not been claimed.
