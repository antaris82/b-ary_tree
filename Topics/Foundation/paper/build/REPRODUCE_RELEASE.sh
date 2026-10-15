#!/usr/bin/env bash
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
SOURCE="$(cd "$HERE/../../lean" && pwd)"
cd "$SOURCE"
printf 'Reproducing against published unpacked Lean source: %s\n' "$PWD"
cat lean-toolchain
bash scripts/verify_release.sh
