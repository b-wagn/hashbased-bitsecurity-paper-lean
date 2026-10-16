import XmssSecurity.Statement.BitSecurity
import XmssSecurity.Statement.Security.EUFCMA
import XmssSecurity.Statement.Scheme.Xmss
-- The only import of the proof layer; see `scripts/check_statement_imports.sh`.
import XmssSecurity.Proof.Main.Unforgeability

/-!
# Standard unforgeability of XMSS: the theorem

This file states and proves the exact classical bit security of XMSS with the checksummed WOTS
encoding under standard unforgeability (EUF-CMA, `Security/EUFCMA.lean`) in the random-oracle
model, for each of the sixteen counting modes that count the adversary's own hash queries. The
rest of `Statement/` contains only definitions; the proof lives under `Proof/`.

A standard forgery must use an epoch/message pair never requested from the signer, including
requests that returned no signature. Bit security and the counting modes are as in
`StrongUnforgeabilityTheorems.lean`.

| Counting mode `Z` (with `hash ∈ Z`) | Exact bits |
|---|---|
| none of `keygen`, `signer`, `verifier` in `Z` (`{hash}` and `{hash, sign}`) | 122 |
| `{hash, signer}` | 123 |
| `{hash, signer, sign}` | 124 |
| `keygen` or `verifier` in `Z` (12 modes) | 127 |

The levels are those of strong unforgeability.

## Why these levels

* The security proofs are those of strong unforgeability: a standard forgery is a strong one.
* 122, 123, 124 bits. Every digest encodes, so a signature for one message already answers half
  of a forgery for any other message at the same epoch. The matching attack requests one
  signature and submits it unchanged for a fresh message. The verifier hashes a fresh leaf and `32`
  tree nodes along the honest authentication path, and each of these `33` fresh hash calls hits the
  honest value with probability `1 / 2^128`; the attack succeeds with probability above
  `32 / 2^128`. Its work is as for the strong attack: `1`, `2`, or `3`.
* 127 bits in the other modes: the neighboring-codeword attack of
  `StrongUnforgeabilityTheorems.lean` forges a fresh message.
-/

namespace XmssSecurity

open SUFCMA

/-- The exact standard-unforgeability classification of XMSS: under every counting mode `Z` that
counts the adversary's own hash queries, XMSS has exactly 127 bits of classical EUF-CMA security
if `Z` counts the hash queries of key generation or verification, and otherwise exactly 124 bits if
`Z` counts the signer's hash queries and the signing queries, 123 bits if it counts the signer's
hash queries only, and 122 bits if it counts neither. -/
theorem xmss_eufCma_exact (Z : Finset QueryKind) (hZ : QueryKind.hash ∈ Z) :
    (EUFCMA.securityGame).HasExactClassicalSecurityBits xmss Z
      (if QueryKind.keygen ∈ Z ∨ QueryKind.verifier ∈ Z then 127
      else if QueryKind.signer ∈ Z ∧ QueryKind.sign ∈ Z then 124
      else if QueryKind.signer ∈ Z then 123
      else 122) :=
  Proof.eufCma_exact_of_hash_mem Z hZ

/-- info: 'XmssSecurity.xmss_eufCma_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_eufCma_exact

end XmssSecurity
