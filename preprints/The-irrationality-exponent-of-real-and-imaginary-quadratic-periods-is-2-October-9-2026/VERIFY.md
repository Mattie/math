# Verification and reproduction

The project pins Lean **4.34.1** and Mathlib **d13f23b723b8a846827a245b89c10fc7d3f11612**. The [source inventory](lean/source-manifest.json) includes every local Lean module and the build/dependency configuration. [Provenance](evidence/source-provenance.json) distinguishes unchanged frozen sources from scoped derivatives.

## Source rebuild

With Git, Python 3, and Elan installed, run from this preprint directory:

```sh
python3 scripts/check-publication.py
cd lean
lake exe cache get
bash verify.sh
```

`verify.sh` explicitly builds `PeriodicFamily.Main`, `Quadratic.RationalFamilies`, `Combined`, `Solution`, and `Audit`, then runs a fresh six-target transitive axiom audit and enforces the standard allowlist. Mathlib's official cache supplies dependency artifacts; omit the cache command for a source-only dependency rebuild. The [fresh verification receipt](evidence/fresh-verification.json) records a completed build of all 1,028 packaged proof modules from an initially empty candidate build directory. Lean, Mathlib, and checking-tool binaries were trusted inputs. Inherited style/deprecation diagnostics are retained in the logs.

For an explicit build of every packaged proof module, run this from `lean` after the source-inventory check and dependency setup:

```sh
python3 - <<'PY'
import json
import subprocess
from pathlib import Path
rows = json.loads(Path('source-manifest.json').read_text(encoding='utf-8'))
modules = [row['path'][:-5].replace('/', '.') for row in rows
           if row['path'].endswith('.lean')
           and row['path'] not in {'lakefile.lean', 'Challenge.lean'}]
subprocess.run(['lake', 'build', *modules], check=True)
PY
bash verify.sh
```

This selects source modules explicitly: Lake's default library targets select their root modules, and these directory-style libraries have no root file. The successful fresh run closes the packaged-source reconstruction gap left by the earlier cached build. It is not a bootstrap of Lean or all upstream dependencies from source.

`Challenge.lean` has six intentional proof placeholders, imports only Mathlib, and is never imported by `Solution.lean`. It is a specification input to the comparator, not an accepted proof library. `StandardBridge.lean` is unchanged. `Challenge.lean` and `Solution.lean` retain the first six original theorem declarations and remove excluded material; no new mathematical theorem has been added. See the [theorem map](evidence/theorem-map.md).

## Fresh six-target verification

The completed October 10, 2026 run built the final `Solution` and its imports from an empty candidate build directory, checked statement and referenced-definition agreement against the independent Mathlib-only `Challenge`, and recorded both Nanoda acceptance and Lean default-kernel acceptance with comparator exit zero. The exact fresh export is 1,279,948,787 bytes, SHA-256 `bf413eeb013b7443f9444d6a3bf2c8d6428ce2fe04d8217172e789a6ba4f6b70`.

The structured export inventory contains all six expected theorem records and exactly `propext`, `Classical.choice`, and `Quot.sound`. Nanoda's unpermitted-axiom hard-error setting was enabled. The final explicit module sweep completed all 1,028 packaged proof modules, and the separate strict six-target axiom audit passed. Every protected source, configuration, tool and dependency identity was checked again. The [receipt and public log derivatives](evidence/fresh-verification.json) retain exact identities and results.

Actual positive, theorem-statement mismatch, forbidden-axiom, and filesystem/Unix-socket boundary controls passed. Separate proof-body controls accepted a valid export and rejected the same parsed theorem with its proof value replaced by its type: Nanoda rejected the definitional-equality check, and Lean reported a declaration type mismatch. An earlier incomplete control fixture failed before either kernel and supplies no rejection evidence. These controls establish the observed cases, not universal checker or sandbox soundness.

The initial supplementary library-name sweep failed on absent root files. Its failed receipt and log are retained; a reviewed continuation explicitly selected every frozen proof module and completed the sweep. The accepted comparison and export were preserved unchanged. The comparison CPU allowance was raised from four to six cores during the build, with memory and isolation settings unchanged. The first source run and supplementary continuation share the same initially empty candidate build state; they are not two separate clean rebuilds.

Lean and Mathlib came from identified trusted compiled artifacts, including a fresh official Mathlib cache fetch. Nanoda and Lean replay share the exporter and comparator frontend. The supplementary source sweep covers every packaged module; the independent two-kernel check covers the six-target exported declaration closure. The [fresh export transport](evidence/fresh-export.json) is retained locally, with compression and decompression identities checked, but has no public download.

## Earlier independent checking

The [sanitized historical summary](evidence/historical-checking.json) describes the completed 2026-10-09 comparison and two-kernel replay of a broader nine-target bundle. Six targets are the declarations presented here. The original bundle also contained three out-of-scope integral targets; their source is not distributed here. The full original export is 1,281,232,401 bytes, SHA-256 `c012401cc4c8562cf23538934c25cc25d5c54e9c811eeced7150d3349610d2ec`.

The maintained comparator accepted statement and referenced-definition agreement, enforced its axiom policy, and recorded both `nanoda kernel accepts the solution` and `Lean default kernel accepts the solution`, with exit zero. The axiom inventory contained only `propext`, `Classical.choice`, and `Quot.sound`. Positive, declaration-mismatch, and forbidden-axiom fixtures behaved as expected; the mismatch fixture tested constant-kind disagreement. Protected writes/truncation, IPv4 connections, Unix socket creation, and parent signaling were blocked in the actual Linux boundary controls, while the allowed build write succeeded. IPv4 socket creation itself was allowed.

The earlier local WSL sandbox failed its boundary probe under Landlock ABI 1. It is **not** isolated acceptance evidence. The accepted run used a different Linux host with Landlock ABI 8 and the recorded restrictions. Both that run and local packaging reuse dependency caches. Controls establish observed behavior, not universal sandbox or kernel soundness.

The comparator source pin is `ca04cfc72b550331658ec314bf47685281bfd4bf`. Although that checkout declares Lean 4.35.0-rc4, its unchanged source and lean4export were built with 4.34.1 for compatibility. lean4export is pinned to `05d43a2bc773b40ecfdebb32294192a5ef756951`; Nanoda to `3a2407216ee84a75f9e1aead6803d0578be06ae7`; Landrun to `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4`. The original record includes scoped 2026-10-09 triage of Nanoda structured-axiom-name and non-hard-error reports: the export's structured names were checked and hard errors were enabled. That is not an exhaustive current checker audit.

## Repeat the independent comparison

The repository's maintained [isolated verification documentation](../../verification/isolated-irrationality/README.md) describes its existing protected build/check arrangement. Use the pinned maintained comparator and its documented isolation on a compatible Linux system; compile its unchanged sources under the package's 4.34.1 toolchain as explained above. The public `lean/comparison.json` selects precisely the six scoped obligations. Run the comparator's maintained positive, mismatch and illegal-axiom fixtures and verify the actual boundary controls before accepting any isolated result. Export/replay and statement comparison must use the same candidate input and enforce the three-axiom policy. Retain fresh command, tool, source, export and result identities. The existing hosted workflow is a reference pattern, not a claim that it already checks this new package.

After the protected dependency setup and successful controls, the observed comparator invocation has this shape (tool variables must point to the pinned compatible builds):

```sh
cd lean
systemd-run --user --wait --pipe --collect \
  --property=RestrictAddressFamilies=~AF_UNIX \
  --working-directory="$PWD" --setenv="PATH=$PATH" \
  --setenv="COMPARATOR_LANDRUN=$COMPARATOR_LANDRUN" \
  --setenv="COMPARATOR_LEAN4EXPORT=$COMPARATOR_LEAN4EXPORT" \
  --setenv="COMPARATOR_NANODA=$COMPARATOR_NANODA" \
  lake env "$COMPARATOR" comparison.json
```

This command is only the final invocation, not a replacement for the protected setup or controls. A locally writable dependency cache or a failing boundary probe invalidates an isolation claim. The source rebuild command above does not need an isolation claim.

The completed fresh run is recorded above under its own six-target export identity. Exact replay of either retained export additionally requires that artifact; see [asset availability](release-assets/README.md). No public-download replay was performed because no public download exists.

## Paper and publication checks

```sh
bash scripts/build-paper.sh
python3 scripts/check-publication.py
```

The paper build uses Python 3, Pandoc, and Tectonic. Publication checks validate source hashes and inventory, local imports, and local Markdown links; they are not proof checking. Mathematical correctness, source reconstruction, semantic comparison, replay, privacy, and distribution availability are distinct claims.

The [publication review receipt](evidence/publication-review.json) records manuscript/PDF identities, visual inspection, and separate automated mathematical and specification/evidence reviews. Its verification revision links the fresh source-build and two-kernel evidence separately from the earlier model reviews. Model reviews are not human peer review.