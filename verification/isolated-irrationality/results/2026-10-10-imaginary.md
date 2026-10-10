# Isolated normalized quadratic-arctangent source verification

The [hosted run](https://github.com/Mattie/math/actions/runs/38008467996) passed
on commit `4aa817179b5a81358dcdefeb1d454a31ab2f2c27`. The exact target was
`OAI.Imaginary.normalized_arctan_sqrt_two_irrationality_and_bound` in module
`Imaginary.FormalConjectures`. It checks irrationality and the exponent-two
approximation bound for `arctan(sqrt(2))/sqrt(2)` against the frozen independent
challenge.

Verification ran from 2026-10-10 01:56:43 UTC to 02:43:23 UTC. Comparator reported
success, and both Nanoda and Lean's default kernel explicitly accepted the solution.
All seven receipt checks passed: tools, isolation, valid proof, statement mismatch,
forbidden axiom, trusted dependencies, and the normalized quadratic-arctangent theorem.

The local archive audit verified:

- The exact run, attempt, commit, case, theorem, runner, frozen inputs and tool pins.
- The original archive digest and all 84 extracted file contents.
- All 56 command-log hashes and 24 retained-file hashes.
- All 943 frozen source-manifest entries and 945 prepared candidate-inventory entries.
- All nine dependency revisions and their clean-source checks.
- Expected negative-control diagnostics, filesystem denials, and Unix-socket denials.
- The generated checking configuration and explicit acceptance by both kernels.

The reviewed runner enforced unchanged candidate inputs, dependency bytes, and tool
binaries before writing its passed receipt. The archive retains the inventory and
recorded identities; it does not contain every compiled dependency or tool binary.

The original [evidence archive](https://github.com/Mattie/math/actions/runs/38008467996/artifacts/11657410395) is also preserved locally.
Its SHA-256 is
`b0f3123f4d2dbc47327858fc51fd1caab1bafc79a313801d12fb3078628abe00`, matching
the digest published for artifact `11657410395`. GitHub reports artifact expiry
at 2027-01-08 00:18:23 UTC. The [structured audit](2026-10-10-imaginary.json) records
the identities and key command logs.

This is successful isolated source verification. Comparator did not retain a new
downloadable proof export. These records summarize the audited run;
existing proofs, pins, exports, and historical receipts are unchanged.
