# Retained exports: availability

The fresh six-target export is distributed in the [October 10 proof-export release](https://github.com/Mattie/math/releases/tag/proof-exports-2026-10-10), targeting paper-package commit `ce265b9dfa4e9f686649d09b00ac11e880b7c483`. The earlier nine-target export remains locally retained only. Rebuilding from the published sources is a separate route.

## Fresh six-target export

| Artifact | Bytes | SHA-256 | Availability |
| --- | ---: | --- | --- |
| Uncompressed NDJSON checker input | 1279948787 | `bf413eeb013b7443f9444d6a3bf2c8d6428ce2fe04d8217172e789a6ba4f6b70` | Decompress the public transport |
| Zstandard transport | 209292318 | `dfdfb837e927dfd72e7249ade14d199c6ba38410627f3329918e160e4a523442` | [Download](https://github.com/Mattie/math/releases/download/proof-exports-2026-10-10/quadratic-family-six-target-export-20261010.ndjson.zst) |

The public transport was downloaded without authentication, fully decompressed, and matched to the exact checker-input size and hash. The [distribution inventory](../evidence/fresh-export-distribution.json) and [download receipt](../evidence/fresh-export-download-20261010.json) record those checks. They add distribution evidence without a new kernel replay. The original [identity record](../evidence/fresh-export.json) and [verification receipt](../evidence/fresh-verification.json) remain unchanged, including their pre-release availability statements.

With `zstd` installed, verify the downloaded archive and its decompressed bytes against the table above:

```sh
sha256sum quadratic-family-six-target-export-20261010.ndjson.zst
zstd -dc quadratic-family-six-target-export-20261010.ndjson.zst > quadratic-family-six-target-export-20261010.ndjson
sha256sum quadratic-family-six-target-export-20261010.ndjson
wc -c quadratic-family-six-target-export-20261010.ndjson*
```

The repository's older `check-release-assets.py` accepts gzip transports only; do not use it for this Zstandard asset.

## Earlier nine-target export

| Artifact | Bytes | SHA-256 | Availability |
| --- | ---: | --- | --- |
| Uncompressed NDJSON checker input | 1281232401 | `c012401cc4c8562cf23538934c25cc25d5c54e9c811eeced7150d3349610d2ec` | Locally retained only |
| Zstandard transport | 209505900 | `e31213df03b832c8932e091dc8d2db3e73d128c42282cbb157f1f8b2dd866829` | Locally retained only |

The retained export includes three out-of-scope integral obligations. No integral development is included in this preprint's proof source. The asset identity is preserved to describe prior checking accurately, not to advertise a separate integral result or a smaller newly checked export.
