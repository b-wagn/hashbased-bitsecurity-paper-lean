#!/usr/bin/env bash
# The statement layer must not depend on the proof layer, except for the three theorem files
# `Statement/*Theorems.lean`, which state the main results and import their proofs.
# Checks that (1) no other statement file imports `XmssSecurity.Proof.*`, and (2) no statement
# file imports a theorem file (which would pull in the proof layer indirectly).
# Usage: scripts/check_statement_imports.sh   (from anywhere)
set -euo pipefail
cd "$(dirname "$0")/.."
theorems='(Correctness|StrongUnforgeability|Unforgeability)Theorems'
import_status=0
while IFS= read -r file; do
  case "$file" in
    XmssSecurity/Statement/CorrectnessTheorems.lean|\
    XmssSecurity/Statement/StrongUnforgeabilityTheorems.lean|\
    XmssSecurity/Statement/UnforgeabilityTheorems.lean)
      forbidden="XmssSecurity\\.Statement\\.$theorems([[:space:]]|$)" ;;
    *) forbidden="XmssSecurity\\.(Proof\\.|Statement\\.$theorems([[:space:]]|$))" ;;
  esac
  if rg -nH "^[[:blank:]]*import[[:blank:]]+$forbidden" "$file"; then
    import_status=1
  else
    rg_status=$?
    if [ "$rg_status" -ne 1 ]; then exit "$rg_status"; fi
  fi
done < <(rg --files XmssSecurity/Statement -g '*.lean')
if [ "$import_status" -ne 0 ]; then
  echo "Unexpected dependencies on the proof layer listed above." >&2
  exit "$import_status"
fi
echo "OK: only the Statement/*Theorems.lean files import the proof layer."
