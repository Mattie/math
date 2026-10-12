# Scoped checker assessment, October 12, 2026

This is a bounded primary-source review and local execution record. The
[completed local run](results/local-replay-2026-10-12.json) passed semantic
comparison and both direct retained-byte replays. This does not assert that every
checker defect is known. Hosted source verification has not been performed.
The new pins retain the unchanged affine package's compatible revisions; no older
package, receipt, or shared checker configuration was edited.

The source compiler and new separately built reader use Lean **4.34.1**,
`5045d0056413266e57c625dcd7c365b10e377c52`. The official
[release notes](https://lean-lang.org/doc/reference/latest/releases/v4.34.1/)
describe runtime fixes relevant to correctness. The archived 4.34.0 reader is
therefore not selected as the primary standalone checker for this extension.
Fresh official compare-API ancestry queries also confirm the 4.34.1 pin includes
the [opaque-value free-variable fix](https://github.com/leanprover/lean4/pull/14498)
and [inductive-declaration fix](https://github.com/leanprover/lean4/pull/14577).

Fresh official compare-API queries returned `status=ahead`, `behind_by=0` for:

| Tool | Selected commit | Included repair | Ahead |
| --- | --- | --- | --- |
| Comparator | `ca04cfc72b550331658ec314bf47685281bfd4bf` | [Quotient post-check](https://github.com/leanprover/comparator/commit/41a09078c793d9d46cdc867a71593bbfe680006e) | 19 |
| lean4export | `05d43a2bc773b40ecfdebb32294192a5ef756951` | [Duplicate-declaration rejection](https://github.com/leanprover/lean4export/commit/b280a889f7342ca71ca537722309c2353a36f63c) | 37 |
| Nanoda | `3a2407216ee84a75f9e1aead6803d0578be06ae7` | [Orphan-recursor rejection](https://github.com/ammkrn/nanoda_lib/commit/8a327a18c3a1401d6ccc1d64053b1397861136e8) | 10 |

The Comparator/exporter commits declare a newer upstream development toolchain;
the maintained local setup explicitly builds those sources using the project's
Lean 4.34.1. Record this build choice and the actual binary hashes, rather than
inferring binary compatibility from a commit label. The existing local binaries
were freshly hashed and match the archived affine receipt.

[Nanoda #37](https://github.com/ammkrn/nanoda_lib/issues/37) remains open:
flattened axiom-name strings can collide. The new route retains Comparator's
structured-name/type gate, plus a separate structured-name export inventory.
Standalone Nanoda acceptance alone is insufficient for the axiom policy.
[Nanoda #39](https://github.com/ammkrn/nanoda_lib/issues/39) also remains open:
the printed success summary can conceal skipped axioms. Use
`unpermitted_axiom_hard_error=true`; the new direct replay configuration also sets
`print_axioms=false`. Require actual exits, controls, and the structured inventory.

**A fresh issue audit found a further selected-pin limitation.**
[Nanoda #47](https://github.com/ammkrn/nanoda_lib/issues/47), opened October 12,
reports an invalid projection accepted by Nanoda. We reproduced it on the exact
selected `3a24072` binary: Nanoda exits zero, while both the ordinary Lean 4.34.1
compiler and the separately built stock 4.34.1 replay reject specifically with
`invalid projection`. The fixture constructs malformed syntax under an explicit
compiler-check bypass; it is never imported by the candidate. See the sanitized
[classification receipt](results/projection-limitation-2026-10-12.json).
Nanoda acceptance is therefore supporting evidence, not a sufficient standalone
certificate. Successful Lean replay of the same retained bytes is mandatory.

The fresh upstream API snapshot identifies Nanoda HEAD as
`0f88b5f382f0f3f08aed4af0dd6c0e48c3fd7a44`, after the October 11 proof-irrelevance
change. Issue 47 also reports the defect on that newer revision, so upgrading
without analysis would not resolve it. The selected older pin also has the
performance differences discussed in
[issue 44](https://github.com/ammkrn/nanoda_lib/issues/44); resource exhaustion is
a failed run, not acceptance. Comparator and exporter pins still matched their
respective upstream HEADs in this refreshed query. No shared pin was changed.

[Comparator #77](https://github.com/leanprover/comparator/issues/77) remains open
and discusses descendants surviving the build process. The author reports no
working exploit; discussion disputes its implications for Comparator soundness.
Our Landrun/systemd probes establish the operations tested, not universal
containment. The local proof is ordinary trusted mathematical source; this work
does not certify arbitrary hostile build scripts.

The new stock reader uses the maintained `Export.Parse` and stock kernel replay
entry point. It regenerates quotient primitives by removing `Quot.mk`,
`Quot.lift`, and `Quot.ind` before replay, matching the established reader.
It has no independent semantic comparator or axiom allowlist; the successful
Comparator run and structured inventory must supply those separate gates.
It shares the Lean kernel family with Comparator. Nanoda supplies the independent
kernel implementation.

The separately built 4.34.1 reader's tiny controls **passed in fresh execution**:
positive proof accepted; negative export parsed, then failed specifically with a
kernel declaration-type mismatch for `validation_control`; Nanoda accepted the
positive and rejected the same one-body mutation with its type-equality check.
The mutation check verifies only the theorem value differs. See
[summary with build/log digests](results/stock-controls-2026-10-12.json),
and [control driver](stock_controls.py). These are checking-route controls,
not acceptance of the denominator theorem.
