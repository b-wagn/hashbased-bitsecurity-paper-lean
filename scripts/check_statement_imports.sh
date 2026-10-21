#!/usr/bin/env bash
# The XMSS and SLH-DSA statement layers must not depend on either proof layer, except
# for the three XMSS Statement/*Theorems.lean files. No statement file may import a
# theorem file, which would pull in proofs indirectly.
# Usage: scripts/check_statement_imports.sh   (from anywhere)
set -euo pipefail
cd "$(dirname "$0")/.."
theorems='(Correctness|StrongUnforgeability|Unforgeability)Theorems'
libraries='(XmssSecurity|SlhDsaSecurity)'

# Prefer ripgrep when it is a real executable; otherwise fall back to grep so the
# check never degrades into a silent pass when rg is unavailable (e.g. in CI or a
# non-interactive shell where rg is only a shell function).
if command -v rg >/dev/null 2>&1 && rg --version >/dev/null 2>&1; then
  list_files() { rg --files XmssSecurity/Statement SlhDsaSecurity/Statement -g '*.lean'; }
  match_import() { rg -nH "^[[:blank:]]*import[[:blank:]]+$1" "$2"; }
else
  list_files() { find XmssSecurity/Statement SlhDsaSecurity/Statement -name '*.lean' -type f; }
  match_import() { grep -nHE "^[[:blank:]]*import[[:blank:]]+$1" "$2"; }
fi

import_status=0
while IFS= read -r file; do
  case "$file" in
    XmssSecurity/Statement/CorrectnessTheorems.lean|\
    XmssSecurity/Statement/StrongUnforgeabilityTheorems.lean|\
    XmssSecurity/Statement/UnforgeabilityTheorems.lean)
      forbidden="$libraries\\.Statement\\.$theorems([[:space:]]|$)" ;;
    *) forbidden="$libraries\\.(Proof\\.|Statement\\.$theorems([[:space:]]|$))" ;;
  esac
  if match_import "$forbidden" "$file"; then
    import_status=1
  else
    match_status=$?
    if [ "$match_status" -ne 1 ]; then exit "$match_status"; fi
  fi
done < <(list_files)
if [ "$import_status" -ne 0 ]; then
  echo "Unexpected dependencies on the proof layer listed above." >&2
  exit "$import_status"
fi
echo "OK: only the three XMSS Statement/*Theorems.lean files import either proof layer."
