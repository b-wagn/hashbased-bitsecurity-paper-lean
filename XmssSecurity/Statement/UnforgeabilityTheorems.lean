import XmssSecurity.Statement.BitSecurity
import XmssSecurity.Statement.Security.EUFCMA
import XmssSecurity.Statement.Scheme.Xmss
-- The only import of the proof layer; see `scripts/check_statement_imports.sh`.
import XmssSecurity.Proof.Main.Unforgeability

/-!
# Standard unforgeability of XMSS: the theorem

This file states and proves the exact classical bit security of XMSS under standard
unforgeability (EUF-CMA, `Security/EUFCMA.lean`) in the random-oracle model, for each of the
sixteen counting modes that count the adversary's own hash queries. The rest of `Statement/`
contains only definitions; the proof lives under `Proof/`.

A standard forgery must use an epoch/message pair never requested from the signer, including
requests that returned no signature. Bit security and the counting modes are as in
`StrongUnforgeabilityTheorems.lean`.

| Counting mode `Z` (with `hash ∈ Z`) | Exact bits |
|---|---|
| `Z = {hash}` | 126 |
| any further kind in `Z` (15 modes) | 127 |

## Why these levels

* 126 bits. The matching attack requests one signature and makes one hash query of its own:
  it queries the encoding of a second, fresh message under the signature's randomness. If that
  encoding decodes, it submits the signature for the second message; otherwise it submits the
  signature for a third fresh message, whose encoding only the verifier computes. Its success
  probability is strictly above `2^-127`, which refutes 127 bits when only its one hash query
  is counted.
* 127 bits in the other modes. Counting any further kind of query at least doubles the replay
  attack's work, so it no longer refutes 127 bits. The matching attack is
  the neighboring-message forgery (the standard-unforgeability analogue of the 127-bit attack
  in `StrongUnforgeabilityTheorems.lean`); it refutes 128 bits even with every kind of query counted.
-/

namespace XmssSecurity

open SUFCMA

/-- The exact standard-unforgeability classification of XMSS: under every counting mode `Z` that
counts the adversary's own hash queries, XMSS has exactly 126 bits of classical EUF-CMA security
if `Z` counts only those, and exactly 127 bits if `Z` counts any further kind of query. -/
theorem xmss_eufCma_exact (Z : Finset QueryKind) (hZ : QueryKind.hash ∈ Z) :
    (EUFCMA.securityGame).HasExactClassicalSecurityBits xmss Z
      (if QueryKind.keygen ∈ Z ∨ QueryKind.signer ∈ Z ∨ QueryKind.verifier ∈ Z ∨
        QueryKind.sign ∈ Z then 127 else 126) :=
  Proof.eufCma_exact_of_hash_mem Z hZ

/-- info: 'XmssSecurity.xmss_eufCma_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_eufCma_exact

end XmssSecurity
