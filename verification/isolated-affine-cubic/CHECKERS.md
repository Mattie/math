# Hosted checker assessment, October 13, 2026

This hosted route verifies the four exact `AffineCubicVerification` wrappers
against [Challenge.lean](Challenge.lean), whose statements use standard Mathlib
definitions and do not import candidate definitions. The permitted axioms are
`propext`, `Classical.choice`, and `Quot.sound`.

## Fresh hosted execution

The [dispatcher](../../.github/workflows/isolated-irrationality.yml) selects
`affine-cubic` on a disposable GitHub-hosted Ubuntu 24.04 VM. It builds the pinned
checker tools in fresh scratch space, records their executable hashes, and
runs positive and negative controls through the actual Landrun/systemd boundary.
The actual dispatcher and prepared standalone template have distinct recorded
hashes; both are protected and retained with the run evidence.

Trusted dependency setup uses the pinned Mathlib sources and official upstream
compiled cache. Candidate sources enter afterward, with no inherited candidate
compiled cache, and are built under isolation against read-only dependencies.
This is a fresh candidate source build, not a from-source rebuild of every
upstream dependency. The frozen source manifest and all dependency, input, and
checker identities must remain unchanged.

The full run requires statement comparison, Lean's default-kernel acceptance,
and Nanoda acceptance of all four wrappers. The inherited receipt key `affine`
means this cubic target. All nine checks must pass: tools, isolation, valid,
mismatch, axiom, imported-admission, dependencies, affine, and protected-inputs.
The proof service is limited to 18,000 seconds, 12 GiB memory, 400% CPU quota,
and four Lean threads within a six-hour job. Setup requires 35 GiB free disk;
the proof phase requires 10 GiB.

## Selected versions and known limits

The frozen [pins](pins.json) retain Lean 4.34.1 at
`5045d0056413266e57c625dcd7c365b10e377c52`, Comparator
`ca04cfc72b550331658ec314bf47685281bfd4bf`, exporter
`05d43a2bc773b40ecfdebb32294192a5ef756951`, and Nanoda
`3a2407216ee84a75f9e1aead6803d0578be06ae7`. Comparator and exporter are built with
the selected Lean toolchain; the exporter dependency revision is also checked.

[Nanoda issue 47](https://github.com/ammkrn/nanoda_lib/issues/47) and its
[repair](https://github.com/ammkrn/nanoda_lib/pull/48) were checked on October 13.
The selected older Nanoda pin lacks the newer projection-name consistency
check. The maintainer states that this name field was not used for soundness
critical reasoning. Lean's kernel supplies its own check in this route.
A separate earlier local replay with newer Nanoda
`735733408022619f5ccf2133e34dd002e8ae861c` is historical supplementary evidence;
it is not execution by the checker selected for this hosted run.

[Nanoda issue 37](https://github.com/ammkrn/nanoda_lib/issues/37) concerns flattened
axiom names, and [issue 39](https://github.com/ammkrn/nanoda_lib/issues/39) concerns
success-message reporting. Comparator's structured-name axiom policy and
forbidden-axiom controls supply the axiom gate here. A Nanoda success string by
itself is insufficient.

[Comparator issue 77](https://github.com/leanprover/comparator/issues/77) concerns
untrusted descendants outliving a build. This route tests the inherited outer
systemd restriction and Landrun boundary: allowed build writes, protected file
and symlink write denial, and UNIX stream/datagram socket denial, alongside
unrestricted positive baselines. These test specific operations, not universal
containment of arbitrary hostile code.

The October 12 compatibility assessment also checked the selected Lean
opaque-value and inductive-declaration fixes, Comparator quotient post-check,
exporter duplicate-declaration rejection, and Nanoda orphan-recursor rejection.
That historical assessment is reused for unchanged pins; the October 13 check
above is a targeted update, not a claim to have audited every checker defect.

## Evidence boundary

This route does not retain a new standalone export or replay historical export
bytes. Its evidence is fresh isolated source execution, exact wrapper comparison,
controls, and both kernel results. Earlier local cache-based replay and separate
stock Lean reader results remain distinct. Only the final run receipt and raw
logs can establish hosted acceptance; preparation tests do not.
