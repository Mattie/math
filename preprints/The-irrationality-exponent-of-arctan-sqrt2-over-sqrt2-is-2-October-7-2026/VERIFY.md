# Reproduce the proof and paper

Use Linux with elan, Git, Python 3, curl, unzip, gzip, a C toolchain, and sufficient disk space for Mathlib and the 1.27 GB textual proof export. Run these commands from this preprint directory. Scripts fetch pinned dependencies; network access is required for a fresh setup.

## Source integrity and Lean

```bash
python3 scripts/check-publication.py
cd lean
bash verify.sh
```

The package pins Lean 4.34.1 and Mathlib in `lean-toolchain` and `lake-manifest.json`. `verify.sh` checks the frozen and supplementary proof hashes, fetches the pinned Mathlib cache, and builds `Imaginary.EndpointAudit` and `Imaginary.FormalConjectures`. It also audits the catalogue theorem's axioms. The supplementary module is not part of the retained export. The recorded final build used an existing native cache with source equality checks; publication preparation did not repeat a fresh network bootstrap.

## Independent checks

From `lean/`, build the tools and use the binary paths printed by the setup script:

```bash
bash setup-independent-tools.sh /absolute/path/to/tools
export LEAN4EXPORT=/absolute/path/to/tools/lean4export/.lake/build/bin/lean4export
export NANODA=/absolute/path/to/tools/nanoda-target/release/nanoda_bin
bash verify-independent.sh /absolute/path/to/evidence
bash verify-negative-control.sh /absolute/path/to/control-evidence
```

To replay the retained exact export, obtain the separately distributed `imaginary-main.ndjson.gz` and put it under `release-assets/`. No release download is claimed here. Its authoritative hash is in [the asset manifest](evidence/release-assets.json). From the preprint directory:

```bash
bash evidence/nanoda/replay-export.sh
bash lean/verify-second-lean.sh
```

The stock Lean script fetches the official 4.34.0 checker, audits the export for forbidden axioms and unsafe/partial declarations, runs positive and ill-typed negative controls, and checks proof bodies at trust level zero. Both replay paths verify the exact retained export identity. The fresh exporter path verifies the locally rebuilt proof; byte-identical re-export is not assumed.

## Manuscript

Install Pandoc and Tectonic, then run:

```bash
bash scripts/build-paper.sh
```

The editable source is `build/manuscript.md`; the generated LaTeX is `build/main.tex`. The checked-in PDF was built with Pandoc 3.6.4 and Tectonic. License scope is described in [LICENSES.md](LICENSES.md).
