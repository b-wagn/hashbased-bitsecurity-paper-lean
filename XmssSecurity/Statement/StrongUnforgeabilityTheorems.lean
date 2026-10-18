import XmssSecurity.Statement.BitSecurity
import XmssSecurity.Statement.Security.SUFCMA
import XmssSecurity.Statement.Scheme.TargetSum
import XmssSecurity.Statement.Scheme.Checksum
import XmssSecurity.Proof.TargetSum.Main.PaperGames
import XmssSecurity.Proof.TargetSum.Scheme.Bridge
import XmssSecurity.Proof.Checksum.Main.PaperGames
import XmssSecurity.Proof.Checksum.Scheme.Bridge

/-!
# Strong unforgeability of XMSS: the theorems

This file states and proves the exact classical bit security of XMSS under strong unforgeability
(SUF-CMA, `Security/SUFCMA.lean`) in the random-oracle model, for each of the sixteen counting
modes that count the adversary's own hash queries, and for both WOTS encodings: the target-sum
encoding (`xmssTargetSum`, `Scheme/TargetSum.lean`) and the encoding with a checksum
(`xmssChecksum`, `Scheme/Checksum.lean`). The rest of `Statement/` contains only definitions;
the proofs live under `Proof/`.

A counting mode `Z` is a set of query kinds (`SUFCMA.QueryKind`): the adversary's signing
queries (`sign`), its own hash queries (`hash`), and the hash queries of key generation
(`keygen`), of the signer (`signer`), and of the final verification (`verifier`). The
adversary's work is the sum of the counts of the kinds in `Z`. "Exactly `b` bits"
(`BitSecurity.lean`) means: every adversary making at most `q ≥ 1` many `Z`-queries wins with
probability at most `q / 2^b`, and some adversary making at most `q ≥ 1` many `Z`-queries wins
with probability more than `q / 2^(b + 1)`. The adversary is probabilistic and adaptive and has
no bound on running time or memory; the probability is over the master seed, the random oracle,
and the adversary's randomness.

| Counting mode `Z` (with `hash ∈ Z`) | Target sum | Checksum |
|---|---|---|
| `{hash}`, `{hash, sign}` | 122 | 122 |
| `{hash, signer}` | 127 | 123 |
| `{hash, signer, sign}` | 127 | 124 |
| `keygen` or `verifier` in `Z` (12 modes) | 127 | 127 |

## Why these levels

* 122 bits. The matching attack makes no hash call of its own and one signing query: it takes
  the signature and replaces the signature value of one chain by a random value. The verifier
  then hashes the fresh value along the rest of that chain, hashes a fresh leaf, and hashes `32`
  fresh tree nodes; each of these `40 - x` fresh hash calls (`x` the chain's digit) hits the
  corresponding honest value with probability `1 / 2^128`, and any such hit makes the forgery
  verify. With the target sum, some digit is at most `4` (the digits sum to `195` over `42`
  chains), so the attack succeeds with probability at least about `36 / 2^128 > 1 / 2^123`. With
  the checksum, the digits of a codeword sum to at most `301`, and a uniformly chosen chain gives
  success probability above `32.4 / 2^128`.
* The signer's hash calls. The target-sum signer retries randomizers until a digest decodes, up to
  `2^32` trials of two hash calls each (about `2^15` on average), so charging the signer makes the
  attack above far too expensive, and the level is 127 as below. The checksum signer makes exactly
  two hash calls (the randomizer and the encoding): the attack's work is `2` when the signer is
  charged and `3` when the requests are charged too, which refutes `124` and `125` bits.
* 127 bits as soon as the hash calls of key generation or of the final verification are counted.
  Key generation makes about `2^40.5` hash calls and a verification at least `55`, so the attack
  above is counted more work than its chances are worth. The matching attack finds a second
  codeword that moves one unit between two chains of a signed codeword, and then a preimage of one
  chain value; its work-to-success ratio is below `2^128` for both encodings, even with every kind
  of query counted.
-/

namespace XmssSecurity

open SUFCMA

/-- The exact strong-unforgeability classification of XMSS with the target-sum encoding: under
every counting mode `Z` that counts the adversary's own hash queries, exactly 127 bits if `Z`
counts any honest-party hash queries (key generation, signer, or verification), and exactly 122
bits otherwise. -/
theorem xmssTargetSum_sufCma_exact (Z : Finset QueryKind) (hZ : QueryKind.hash ∈ Z) :
    (SUFCMA.securityGame).HasExactClassicalSecurityBits xmssTargetSum Z
      (if QueryKind.keygen ∈ Z ∨ QueryKind.signer ∈ Z ∨ QueryKind.verifier ∈ Z then 127 else 122) := by
  rw [TargetSum.xmssTargetSum_eq]
  exact TargetSum.Proof.sufCma_exact_of_hash_mem Z hZ

/-- The exact strong-unforgeability classification of XMSS with the checksummed encoding: under
every counting mode `Z` that counts the adversary's own hash queries, exactly 127 bits if `Z`
counts the hash queries of key generation or of verification; otherwise exactly 124 bits if `Z`
counts the signer's hash queries and the signing queries, 123 bits if it counts only the signer's
hash queries, and 122 bits if it counts neither. -/
theorem xmssChecksum_sufCma_exact (Z : Finset QueryKind) (hZ : QueryKind.hash ∈ Z) :
    (SUFCMA.securityGame).HasExactClassicalSecurityBits xmssChecksum Z
      (if QueryKind.keygen ∈ Z ∨ QueryKind.verifier ∈ Z then 127
      else if QueryKind.signer ∈ Z ∧ QueryKind.sign ∈ Z then 124
      else if QueryKind.signer ∈ Z then 123
      else 122) := by
  rw [Checksum.xmssChecksum_eq]
  exact Checksum.Proof.sufCma_exact_of_hash_mem Z hZ

/-- info: 'XmssSecurity.xmssTargetSum_sufCma_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmssTargetSum_sufCma_exact

/-- info: 'XmssSecurity.xmssChecksum_sufCma_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmssChecksum_sufCma_exact

end XmssSecurity
