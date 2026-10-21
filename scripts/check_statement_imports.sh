#!/usr/bin/env bash
# The XMSS and SLH-DSA statement layers must not depend on either proof layer, except
# for the three XMSS Statement/*Theorems.lean files. No statement file may import a
# theorem file, which would pull in proofs indirectly.
# Usage: scripts/check_statement_imports.sh   (from anywhere)
set -euo pipefail
cd "$(dirname "$0")/.."
theorems='(Correctness|StrongUnforgeability|Unforgeability)Theorems'
libraries='(XmssSecurity|SlhDsaSecurity)'
import_status=0
while IFS= read -r file; do
  case "$file" in
    XmssSecurity/Statement/CorrectnessTheorems.lean|\
    XmssSecurity/Statement/StrongUnforgeabilityTheorems.lean|\
    XmssSecurity/Statement/UnforgeabilityTheorems.lean)
      forbidden="$libraries\\.Statement\\.$theorems([[:space:]]|$)" ;;
    *) forbidden="$libraries\\.(Proof\\.|Statement\\.$theorems([[:space:]]|$))" ;;
  esac
  if rg -nH "^[[:blank:]]*import[[:blank:]]+$forbidden" "$file"; then
    import_status=1
  else
    rg_status=$?
    if [ "$rg_status" -ne 1 ]; then exit "$rg_status"; fi
  fi
done < <(rg --files XmssSecurity/Statement SlhDsaSecurity/Statement -g '*.lean')
if [ "$import_status" -ne 0 ]; then
  echo "Unexpected dependencies on the proof layer listed above." >&2
  exit "$import_status"
fi
echo "OK: only the three XMSS Statement/*Theorems.lean files import either proof layer."
