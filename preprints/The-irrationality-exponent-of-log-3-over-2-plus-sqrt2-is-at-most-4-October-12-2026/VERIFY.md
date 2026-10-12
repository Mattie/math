# Verification status

This October 12 extension has a separate source and evidence identity from the inherited affine package. Earlier acceptance of the old integral-data theorem does not certify the new endpoint.

The new pilot and arbitrary-data endpoint compiled under Lean 4.34.1 with strict warning settings. Ten source files are frozen by [SHA-256 inventory](../../formalizations/AffineDenominators/evidence/proof-source-sha256.json), and a transitive axiom-policy audit passed for all seven public endpoints with rejection controls.

The [fresh local run](../../verification/isolated-affine-denominators/results/local-replay-2026-10-12.json) passed all eleven checking gates on October 12, 2026. Six statements passed independent specification comparison and both Comparator kernel checks. Nanoda and a separately built stock Lean 4.34.1 reader then accepted the same retained export. The [export inventory](../../verification/isolated-affine-denominators/results/export-inventory-2026-10-12.json) contains 112854 serialized declarations, proof bodies for all six public and six comparison targets, and exactly `propext`, `Quot.sound`, and `Classical.choice` as structured axiom names.

The 1281194270-byte export has SHA-256 `fd0f5d689cc5f04f723d4c105a8da84e0d1f8a4c7356cf01c9db3afeac9f5dd6`. It and the raw diagnostic evidence are retained privately; no public export download or public-download replay is claimed. The public [evidence index](../../verification/isolated-affine-denominators/results/evidence-index-2026-10-12.json) identifies those artifacts. The local run rebuilt the new modules while reusing identified inherited and upstream caches; it does not establish a complete build from source.

The exact pinned Nanoda version accepts a known malformed-projection diagnostic that both Lean checking routes reject. Its acceptance is supplementary; the successful stock Lean replay is required. The [checker assessment](../../verification/isolated-affine-denominators/CHECKERS.md) records this confirmed limitation, shared dependencies, controls and tool identities.

The required targets include the literal general degree-four endpoint, the pilot's eventual and explicit lower bounds, irrationality, the custom supremum exponent, and the standard Mathlib `LiouvilleWith` exclusion. The [claim map](theorem-map.json) records their names.

The [isolated source verifier](../../verification/isolated-affine-denominators/) and manual dispatch route are prepared, with eleven preparation tests passing. Public push and dispatch are not yet authorized for this extension. Fresh hosted execution, its evidence audit, GitHub-rendered Markdown and public retrieval remain pending.

Independent mathematical and specification reviews found no remaining mathematical or statement defect in the frozen scope. Blind manuscript review was followed by source correspondence review; three exposition clarifications were applied. The completed final evidence audit checked the original logs, exact source and executed-adapter identities, and all 120 locally retained indexed files with no hash or size mismatch. The full export is the one remotely retained indexed artifact. Model review is not human peer review, and no optimality or historical-priority claim is made.
