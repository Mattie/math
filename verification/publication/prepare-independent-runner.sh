#!/usr/bin/env bash
# Reserve room for tools, dependency builds, and all retained proof exports.
set -euo pipefail

# Cleanup is confined to a disposable GitHub-hosted Ubuntu 24.04 VM.
if [[ "${GITHUB_ACTIONS:-}" != true || "${RUNNER_ENVIRONMENT:-}" != github-hosted ||
      "${RUNNER_OS:-}" != Linux || "${ImageOS:-}" != ubuntu24 ]]; then
  echo 'Refusing SDK cleanup outside the expected disposable hosted runner.' >&2
  exit 1
fi
: "${RUNNER_TEMP:?RUNNER_TEMP must identify the build filesystem}"
required=$((35 * 1024 * 1024 * 1024))

free_bytes() {
  local available
  available=$(df -PB1 "$RUNNER_TEMP" | awk 'NR == 2 {print $4}')
  if [[ ! "$available" =~ ^[0-9]+$ ]]; then
    echo 'Could not determine available build disk space.' >&2
    return 1
  fi
  printf '%s' "$available"
}

before=$(free_bytes)
printf 'Available before preparation: %s bytes; required: %s bytes (35 GiB).\n' "$before" "$required"
if (( before < required )); then
  # These SDKs are unused by the pinned Bash/Python/Lean/Rust workflow.
  # Keep system compilers, runner executables, repository, and proof work intact.
  sudo rm -rf -- /usr/local/lib/android /usr/share/dotnet /opt/ghc /opt/hostedtoolcache
fi
after=$(free_bytes)
printf 'Available after preparation: %s bytes.\n' "$after"
if (( after < required )); then
  echo '::error::Independent replay needs at least 35 GiB free before tool setup.' >&2
  exit 1
fi
echo 'PASS: independent replay disk capacity gate.'
