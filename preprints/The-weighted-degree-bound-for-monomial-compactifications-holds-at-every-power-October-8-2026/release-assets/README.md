# Proof export

The compressed selected proof export is prepared outside the tracked source
files. Its uncompressed identity and compressed transport identity are listed in
[the release-asset manifest](../evidence/release-assets.json).

Preparation does not imply that a GitHub release asset has been uploaded.
The source and verification instructions remain usable without an asset download.
To regenerate an export, use `scripts/export.sh` after `lean/verify.sh`.
