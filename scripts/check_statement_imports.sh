#!/usr/bin/env bash
# The statement layer must not depend on the proof layer, except for the two theorem files
# `Statement/*Theorems.lean`, which state the main results and import their proofs.
# Checks that (1) no other statement file imports `XmssSecurity.Proof.*`, and (2) no statement
# file imports a theorem file (which would pull in the proof layer indirectly).
# Usage: scripts/check_statement_imports.sh   (from anywhere)
set -euo pipefail
cd "$(dirname "$0")/.."
bad=$(grep -rlE '^import XmssSecurity\.Proof' XmssSecurity/Statement --include='*.lean' \
  | grep -vE 'Theorems\.lean$' || true)
bad="$bad$(grep -rlE '^import XmssSecurity\.Statement\.[A-Za-z]*Theorems$' XmssSecurity/Statement \
  --include='*.lean' || true)"
if [ -n "$bad" ]; then
  echo "Statement files depending on the proof layer:" >&2
  echo "$bad" >&2
  exit 1
fi
echo "OK: only the Statement/*Theorems.lean files import the proof layer."
