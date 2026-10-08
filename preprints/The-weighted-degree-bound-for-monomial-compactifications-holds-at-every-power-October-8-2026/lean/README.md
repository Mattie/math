# Lean overlay

The five `Degree/` modules add an all-power coefficient theorem to the pinned
rational-logarithm project. They do not change the inherited proof library.
See [verification instructions](../VERIFY.md) for the dependency revision,
native checking command, selected export, and both replay routes.

The principal concrete theorem is `Degree.monomial_all_supportBound`.
`Degree.logarithm_all_supportBound` handles the shared construction in the four
Casper preprints, and `Degree.admissible_all_supportBound` handles the released
π library's admissible compactification. The affine coordinates are fixed; the
theorems quantify over all natural bundle powers, frames, and global sections.
