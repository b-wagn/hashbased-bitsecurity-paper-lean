import XmssSecurity.Statement.BitSecurity
import XmssSecurity.Statement.Security.EUFCMA
import XmssSecurity.Statement.Scheme.TargetSum
import XmssSecurity.Statement.Scheme.Checksum
import XmssSecurity.Proof.TargetSum.Main.PaperGames
import XmssSecurity.Proof.TargetSum.Scheme.Bridge
import XmssSecurity.Proof.Checksum.Main.PaperGames
import XmssSecurity.Proof.Checksum.Scheme.Bridge

/-!
# Standard unforgeability of XMSS: the theorems

This file states and proves the exact classical bit security of XMSS under standard
unforgeability (EUF-CMA, `Security/EUFCMA.lean`) in the random-oracle model, for each of the
sixteen counting modes that count the adversary's own hash queries, and for both WOTS encodings
(`xmssTargetSum` and `xmssChecksum`). The rest of `Statement/` contains only definitions; the
proofs live under `Proof/`.

A standard forgery must use an epoch/message pair never requested from the signer, including
requests that returned no signature. Bit security and the counting modes are as in
`StrongUnforgeabilityTheorems.lean`.

| Counting mode `Z` (with `hash ∈ Z`) | Target sum | Checksum |
|---|---|---|
| `{hash}` | 126 | 122 |
| `{hash, sign}` | 127 | 122 |
| `{hash, signer}` | 127 | 123 |
| `{hash, signer, sign}` | 127 | 124 |
| `keygen` or `verifier` in `Z` (12 modes) | 127 | 127 |

## Why these levels

* With the target sum, most digests do not decode, and a forgery for a new message needs a new
  digest that decodes. 126 bits for `{hash}`: the matching attack requests one signature and
  makes one hash query of its own: it queries the encoding of a second, fresh message under the
  signature's randomness. If that encoding decodes, it submits the signature for the second
  message; otherwise it submits the signature for a third fresh message, whose encoding only the
  verifier computes. Its success probability is strictly above `2^-127`. Counting any further kind
  of query at least doubles its work; in those modes the neighboring-codeword attack of
  `StrongUnforgeabilityTheorems.lean` gives the matching 127 bits.
* With the checksum, every digest encodes, so a signature for one message already answers half of
  a forgery for any other message at the same epoch, and the levels are those of strong
  unforgeability. The matching attack requests one signature and submits it unchanged for a fresh
  message. The verifier hashes a fresh leaf and `32` tree nodes along the honest authentication
  path, and each of these `33` fresh hash calls hits the honest value with probability
  `1 / 2^128`; the attack succeeds with probability above `32 / 2^128`. Its work is as for the
  strong attack: `1`, `2`, or `3`.
-/

namespace XmssSecurity

open SUFCMA

/-- The exact standard-unforgeability classification of XMSS with the target-sum encoding: under
every counting mode `Z` that counts the adversary's own hash queries, exactly 126 bits if `Z`
counts only those, and exactly 127 bits if `Z` counts any further kind of query. -/
theorem xmssTargetSum_eufCma_exact (Z : Finset QueryKind) (hZ : QueryKind.hash ∈ Z) :
    (EUFCMA.securityGame).HasExactClassicalSecurityBits xmssTargetSum Z
      (if QueryKind.keygen ∈ Z ∨ QueryKind.signer ∈ Z ∨ QueryKind.verifier ∈ Z ∨
        QueryKind.sign ∈ Z then 127 else 126) := by
  rw [TargetSum.xmssTargetSum_eq]
  exact TargetSum.Proof.eufCma_exact_of_hash_mem Z hZ

/-- The exact standard-unforgeability classification of XMSS with the checksummed encoding, the
same as for strong unforgeability (`xmssChecksum_sufCma_exact`). -/
theorem xmssChecksum_eufCma_exact (Z : Finset QueryKind) (hZ : QueryKind.hash ∈ Z) :
    (EUFCMA.securityGame).HasExactClassicalSecurityBits xmssChecksum Z
      (if QueryKind.keygen ∈ Z ∨ QueryKind.verifier ∈ Z then 127
      else if QueryKind.signer ∈ Z ∧ QueryKind.sign ∈ Z then 124
      else if QueryKind.signer ∈ Z then 123
      else 122) := by
  rw [Checksum.xmssChecksum_eq]
  exact Checksum.Proof.eufCma_exact_of_hash_mem Z hZ

/-- info: 'XmssSecurity.xmssTargetSum_eufCma_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmssTargetSum_eufCma_exact

/-- info: 'XmssSecurity.xmssChecksum_eufCma_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmssChecksum_eufCma_exact

end XmssSecurity
