# Source and verification provenance

This package preserves the verified proof bytes. `evidence/source-sha256.json`
records 969 source/specification files: 924 inherited Lean sources, 26 quadratic
overlay modules, 15 affine modules, three comparison modules, and the Comparator
configuration. The two affine audit modules are included among the 15; the
actual exported affine proof closure contains 13 affine proof modules.

The inherited source pin is [Mattie/math, commit
0cfe10002ea95c45721b93d18bffbe2c3bbbcbbd](https://github.com/Mattie/math/tree/0cfe10002ea95c45721b93d18bffbe2c3bbbcbbd/preprints/The-irrationality-exponent-of-positive-rational-logarithms-is-2-October-7-2026/lean).
It incorporates OpenAI's `OAI.NumberTheory.PiExponent` library at
[adc7f1241b42e322a6451854ab7e4b4c146bf78a](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a).
The rational-logarithm and quadratic-logarithm extensions supply the inherited
determinant construction and estimates. Their role is mathematical as well as
technical; this package does not claim a proof independent of that work.

The affine and quadratic overlay sources were taken from the frozen verification
inputs of October 10, 2026 (checks continued on October 11 UTC). All copied source
hashes were compared with those inputs. The package's Lake configuration and
portable scripts are new packaging files; they are not part of the earlier
proof export. The inherited Lake lockfile and toolchain pin are unchanged.

| Component | Pin |
| --- | --- |
| Lean | 4.34.1, `5045d0056413266e57c625dcd7c365b10e377c52` |
| Mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612` |
| Comparator | `ca04cfc72b550331658ec314bf47685281bfd4bf` |
| lean4export used for the checked export | `05d43a2bc773b40ecfdebb32294192a5ef756951` |
| Rust Nanoda | `3a2407216ee84a75f9e1aead6803d0578be06ae7` |
| Landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` |

The proof compiler and primary Lean checker are from the same Lean 4.34.1
kernel family. Rust Nanoda is an independently implemented kernel. The
supplemental 4.34.0 reader supplies an additional body replay in the Lean family.

The evidence JSON files are sanitized summaries of retained original receipts;
they remove machine paths and process metadata. Their original receipt hashes
are recorded explicitly. `evidence/comparator.log` preserves the original
comparison/build output except its machine-specific first service line. The
summaries' `receipts` keys identify private original records, not package-relative
files. No original receipt hash is presented as a hash of a sanitized copy.

The package is a formal proof artifact, not a journal submission or a claim of
exhaustive novelty. The existing independent model reviews covered the unchanged
mathematics and specification. This packaging step adds source identity and
reproduction checks; it does not add human peer review.
