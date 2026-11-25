# Verify the proof

The [proof archive](lean-proof.zip) and the [unpacked proof](lean/README.md) contain the same 30 files. To verify the archive and check the numerical bound from the preprint directory, run these commands with Python 3 and GNU coreutils.

```sh
echo '56a3c7643dabdc4225ca41e92c4cab8530c8408cdc71184f18780759d91b80b2  lean-proof.zip' | sha256sum -c -
(cd lean && sha256sum -c SHA256SUMS)
python3 check_rate.py
```

The numerical check rounds each term down using integer arithmetic and verifies the strict inequality for the exact rational bound. For a Lean source build on Linux with Bash and Elan, run the command below. The [proof README](lean/README.md) lists the toolchain, dependencies and optional argument for reusing a pinned upstream checkout.

```sh
bash lean/reproduce.sh
```

Alternatively, extract the archive with `python3 -m zipfile -e lean-proof.zip extracted` and run `bash extracted/pi2-window-proof/reproduce.sh`. Each replay checks the source manifest, reconstructs three modules from pinned upstream inputs and audits the axioms of the five declarations in the [theorem map](theorem-map.json).

Run `python3 -I scripts/check-publication.py` to check the packaged files against their recorded hashes, verify the archive against the unpacked proof, and check the article links and theorem map.

## Hosted verification on November 25, 2026

GitHub Actions rebuilt 71 solution modules on Ubuntu 24.04 at commit `02d402999844a7b9524c1668d54e6314979c7569` with the official Mathlib cache. Lake compared all five named declarations in the [theorem map](theorem-map.json) with an independently compiled challenge. The statements matched with zero definition holes and only the three permitted axioms. Nanoda and Lean’s default kernel both accepted the combined solution. The checker accepted the positive control and rejected changes to a statement and a definition, an extra axiom, and an ill-typed proof. [Run 45713249120, attempt 1](https://github.com/Mattie/math/actions/runs/45713249120/job/139552735865) · [Pinned verification sources](https://github.com/Mattie/math/tree/02d402999844a7b9524c1668d54e6314979c7569/verification/prime-window)

The combined solution export was 650,733,862 bytes with SHA-256 `52edb0fe036b0cd5ecf8b4946707c47103756c1534a570142a64f59ea3116ac2`. The retained Actions artifact contains the machine-readable receipt and the 93 command logs. Its ZIP has SHA-256 `a6eed2288b6c343f53dabd0e7955fd002907611e62ef8435fbb319ef75ccd45c`. [Download the retained evidence](verification/hosted-evidence.zip)

## November 23 source and kernel checks

Lean 4.35.0-rc4 compiled the commented proof with Mathlib at commit `1f414401f69059aa7eead47b53ee40bd38455eeb`. Each endpoint reported exactly `propext`, `Classical.choice` and `Quot.sound`. Lake compared all five endpoints with independently written statements and found zero definition holes. The two fresh exports matched the previously verified proof bytes. Nanoda 0.4.32 and a separately built stock Lean kernel with an export-reader backport each accepted both exports. Both checkers rejected a parsed, ill-typed control.

| Export | Endpoints | Declarations checked by Nanoda | SHA-256 of uncompressed export |
| --- | ---: | ---: | --- |
| WindowFinal | 3 | 83,055 | `f0d2e8aa4a9fc7cabd549c3d0e00ed44669ebef2823e5d16360963c0d5c44994` |
| WindowCatalogue | 2 | 83,057 | `cdc0bd85760609b17d4405a1684138cc2e5d7cfd06c21e72430c6c26324f7daa` |

The verification run used cached dependencies. The source replay above rebuilds the proof and checks its axiom reports. The export hashes identify the additional recorded comparisons and kernel checks.

## Build the paper

Run `python3 scripts/build.py` with Tectonic 0.17.0+20260731 and its TeX support files. Pass `--tectonic /path/to/tectonic` to select the executable. The script fixes `SOURCE_DATE_EPOCH=1795564800`, compiles [the LaTeX source](build/main.tex), writes [paper.pdf](paper.pdf) and records the input and output hashes in the [build receipt](build/receipt.json).
