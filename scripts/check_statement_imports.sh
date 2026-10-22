#!/usr/bin/env bash
# The statement layer must not depend on the proof layer, except for the files in
# `Statement/Theorems/`, which state the main results and import their proofs.
# Checks that (1) no other statement file imports `Xmss.Proof.*`, and (2) no statement
# file imports a theorem module (which would pull in the proof layer indirectly).
# Usage: scripts/check_statement_imports.sh   (from anywhere)
set -euo pipefail
cd "$(dirname "$0")/.."
theorems='Statement\.Theorems\.'
import_status=0
while IFS= read -r file; do
  case "$file" in
    Xmss/Statement/Theorems/*) forbidden="Xmss\\.$theorems" ;;
    *) forbidden="Xmss\\.(Proof\\.|$theorems)" ;;
  esac
  if grep -nHE "^[[:blank:]]*import[[:blank:]]+$forbidden" "$file"; then
    import_status=1
  else
    grep_status=$?
    if [ "$grep_status" -ne 1 ]; then exit "$grep_status"; fi
  fi
done < <(find Xmss/Statement -name '*.lean' -type f | sort)
if [ "$import_status" -ne 0 ]; then
  echo "Unexpected dependencies on the proof layer listed above." >&2
  exit "$import_status"
fi
echo "OK: only the Statement/Theorems/ files import the proof layer."
