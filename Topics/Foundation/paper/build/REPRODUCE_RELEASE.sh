#!/usr/bin/env bash
# Reproducer; does not modify the immutable archived file.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
TARGET="${1:-$HERE/reproduction_tree}"
mkdir -p "$TARGET"
tar -xzf "$HERE/evidence/task06_frozen_source.tar.gz" -C "$TARGET"
cd "$TARGET/output-final_aristotle"
chmod +x scripts/*.sh
printf 'Running from %s\n' "$PWD"
cat lean-toolchain
bash scripts/verify_release.sh
