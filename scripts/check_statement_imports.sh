#!/usr/bin/env bash
# For each library (Xmss, SLH-DSA-128s), the statement layer must not depend on the proof layer,
# except for the files in `Statement/Theorems/`, which state the main results and import their
# proofs. Checks that (1) no other statement file imports `<Lib>.Proof.*`, and (2) no statement
# file imports a theorem module (which would pull in the proof layer indirectly).
# Usage: scripts/check_statement_imports.sh   (from anywhere)
set -euo pipefail
cd "$(dirname "$0")/.."
theorems='Statement\.Theorems\.'
import_status=0
for lib in Xmss SLH-DSA-128s; do
  case "$lib" in *-*) mod="«$lib»" ;; *) mod="$lib" ;; esac
  while IFS= read -r file; do
    case "$file" in
      "$lib"/Statement/Theorems/*) forbidden="$mod\\.$theorems" ;;
      *) forbidden="$mod\\.(Proof\\.|$theorems)" ;;
    esac
    if grep -nHE "^[[:blank:]]*import[[:blank:]]+$forbidden" "$file"; then
      import_status=1
    else
      grep_status=$?
      if [ "$grep_status" -ne 1 ]; then exit "$grep_status"; fi
    fi
  done < <(find "$lib"/Statement -name '*.lean' -type f | sort)
done
if [ "$import_status" -ne 0 ]; then
  echo "Unexpected dependencies on the proof layer listed above." >&2
  exit "$import_status"
fi
echo "OK: only the Statement/Theorems/ files import the proof layer."
