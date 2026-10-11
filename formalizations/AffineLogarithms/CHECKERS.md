# Checker versions, controls, and limits

Assessment date: October 10, 2026 (America/Chicago). This is a bounded review
of the selected revisions, not a claim that every checker bug is known or ruled
out. Pins and executed binary hashes are in
[checker-receipt.json](evidence/checker-receipt.json).

## Primary Lean and supplemental historical reader

The primary build and Comparator use Lean 4.34.1,
`5045d0056413266e57c625dcd7c365b10e377c52`. The earlier revision audit confirmed
that this pin and the supplemental Lean 4.34.0 pin descend from the fixes for
[free variables in opaque values](https://github.com/leanprover/lean4/pull/14498)
and the [missing inductive-declaration check](https://github.com/leanprover/lean4/pull/14577).

**The historical Lean 4.34.0 reader lacks the runtime fixes in 4.34.1.**
Those fixes address reference-count overflow, sharing, and deletion behavior;
the official release notes identify possible effects on kernel correctness and
recommend upgrading. The current 4.34.1 result is the primary Lean evidence.
The older reader is retained to reproduce a supplemental historical result,
not recommended as the sole checker for new or hostile inputs.
[Lean 4.34.1 release notes](https://lean-lang.org/doc/reference/latest/releases/v4.34.1/).

The reader parses an export and replays declarations into an empty kernel
environment. It removes `Quot.mk`, `Quot.lift`, and `Quot.ind` because adding
`Quot` regenerates those primitives. It has no independent permitted-axiom policy,
statement comparison, or modern quotient post-check. The original maintained
Comparator run supplies those checks. Two Lean versions remain members of the
same kernel family; Rust Nanoda supplies implementation diversity.

## Nanoda

The recorded Nanoda revision is `3a2407216ee84a75f9e1aead6803d0578be06ae7`.
It contains the orphan-recursor rejection fix checked in the original version
audit, but the selected revision has a known axiom-name collision issue:
flattening a structured Lean name can confuse a single quoted name component
with an ordinary dotted name. The upstream issue remained open when checked
for this package revision. A permitted-name string list by itself is therefore
insufficient assurance. The original Comparator compared structured names and
types before invoking Nanoda, and the retained export inventory separately
records exactly `propext`, `Quot.sound`, and `Classical.choice` as structured
names. [Nanoda issue 37](https://github.com/ammkrn/nanoda_lib/issues/37).

The same pin also has a success-message/pretty-printer issue that can hide
reports of skipped axioms. Our configuration uses
`unpermitted_axiom_hard_error=true`; the exit status, actual controls, structured
inventory, and Comparator gates carry the evidence, rather than a success
message alone. [Nanoda issue 39](https://github.com/ammkrn/nanoda_lib/issues/39).

The portable replay script accepts only the exact previously inventoried export
hash. It is not an unrestricted replacement for the structured-name Comparator
gate. Its controls exercise proof-body acceptance and rejection; they do not
certify the absence of all possible name or kernel bugs.

## Comparator and isolation

The pinned Comparator includes its quotient post-check, and the selected
exporter includes duplicate-declaration rejection, as established in the
original source-revision audit. The run tested allowed and denied writes and
AF_UNIX socket restrictions. These are concrete boundary checks, not proof of
containment against every hostile build process. In particular, the reported
[descendant-process limitation](https://github.com/leanprover/comparator/issues/77)
was still open on the assessment date.

The proof sources in this package are ordinary local mathematical sources.
Neither a fresh working directory nor the portable build script is advertised
as a hostile-submission sandbox. Checker installation and isolation configuration
remain separate from rebuilding and auditing these sources.

## Axiom audit controls

`scripts/build.py` invokes the same `scripts/audit_axioms.py` policy command used
by `scripts/audit_controls.py`. The control suite compiles a valid imported proof,
an imported admitted proof, and an imported extra-axiom proof. The importing
audit modules elaborate successfully; the policy must accept the first and
reject the latter two specifically for `sorryAx` and `forbidden_control`.
It also rejects missing, truncated, conflicting, and malformed-after-valid
diagnostics. Identical repeated reports are allowed because Lake can replay
diagnostics before a direct audit prints them again.

This parser enforces a policy on trusted Lean diagnostic output. It does not
authenticate arbitrary log text or replace the structured export comparison.
The final mathematical sources are unchanged by these tooling checks.

The original maintained Comparator route was also exercised with valid,
imported-admission, and imported-extra-axiom fixtures using the same recorded
checker binaries. The valid fixture passed both kernels; the latter two were
rejected by the Comparator's axiom gate for `sorryAx` and `forbidden_control`.
That gate runs before proof-body replay for those rejected fixtures. See the
[additional control receipt](evidence/pre-pr/comparator-controls/receipt.json).
