import XmssSecurity.Statement.BitSecurity
import XmssSecurity.Statement.Security.SUFCMA
import XmssSecurity.Statement.Scheme.Xmss
-- The only import of the proof layer; see `scripts/check_statement_imports.sh`.
import XmssSecurity.Proof.Main.StrongUnforgeability

/-!
# Strong unforgeability of XMSS: the theorem

This file states and proves the exact classical bit security of XMSS with the checksummed WOTS
encoding under strong unforgeability (SUF-CMA, `Security/SUFCMA.lean`) in the random-oracle model,
for each of the sixteen counting modes that count the adversary's own hash queries. The rest of
`Statement/` contains only definitions; the proof lives under `Proof/`.

A counting mode `Z` is a set of query kinds (`SUFCMA.QueryKind`): the adversary's signing
queries (`sign`), its own hash queries (`hash`), and the hash queries of key generation
(`keygen`), of the signer (`signer`), and of the final verification (`verifier`). The
adversary's work is the sum of the counts of the kinds in `Z`. "Exactly `b` bits"
(`BitSecurity.lean`) means: every adversary making at most `q ≥ 1` many `Z`-queries wins with
probability at most `q / 2^b`, and some adversary making at most `q ≥ 1` many `Z`-queries wins
with probability more than `q / 2^(b + 1)`. The adversary is probabilistic and adaptive and has
no bound on running time or memory; the probability is over the master seed, the random oracle,
and the adversary's randomness.

| Counting mode `Z` (with `hash ∈ Z`) | Exact bits |
|---|---|
| none of `keygen`, `signer`, `verifier` in `Z` (`{hash}` and `{hash, sign}`) | 122 |
| `{hash, signer}` | 123 |
| `{hash, signer, sign}` | 124 |
| `keygen` or `verifier` in `Z` (12 modes) | 127 |

## Why these levels

* 122, 123, 124 bits. The matching attack makes no hash call of its own and one signing query: it
  takes the signature and replaces the signature value of a uniformly chosen chain by a random
  value. The verifier then hashes the fresh value along the rest of that chain, hashes a fresh
  leaf, and hashes `32` fresh tree nodes; each of these `40 - x` fresh hash calls (`x` the chain's
  digit) hits the corresponding honest value with probability `1 / 2^128`, and any such hit makes
  the forgery verify. The digits of a codeword sum to at most `301`, so on average over the `46`
  chains the attack succeeds with probability above `32.4 / 2^128 > 1 / 2^123`. Its work is one
  signing request, which costs the signer two hash calls (the randomizer and the encoding): `1`
  when only requests are charged, `2` when the signer is charged, and `3` when both are, which
  refutes `123`, `124`, and `125` bits respectively.
* 127 bits as soon as the hash calls of key generation or of the final verification are counted.
  Key generation makes about `2^41` hash calls and a verification at least `55`, so the attack
  above is counted more work than its chances are worth. The matching attack (Remark 5.3 of the
  leanVM XMSS document,
  https://github.com/leanEthereum/leanVM/releases/download/doc-latest/XMSS.pdf) finds a second
  codeword that moves one unit between two chains of a signed codeword (every codeword has at
  least `42` such neighbors), and then a preimage of one chain value; its work-to-success ratio is
  below `2^128`, even with every kind of query counted.
-/

namespace XmssSecurity

open SUFCMA

/-- The exact strong-unforgeability classification of XMSS: under every counting mode `Z` that
counts the adversary's own hash queries, XMSS has exactly 127 bits of classical SUF-CMA security
if `Z` counts the hash queries of key generation or verification, and otherwise exactly 124 bits if
`Z` counts the signer's hash queries and the signing queries, 123 bits if it counts the signer's
hash queries only, and 122 bits if it counts neither. -/
theorem xmss_sufCma_exact (Z : Finset QueryKind) (hZ : QueryKind.hash ∈ Z) :
    (SUFCMA.securityGame).HasExactClassicalSecurityBits xmss Z
      (if QueryKind.keygen ∈ Z ∨ QueryKind.verifier ∈ Z then 127
      else if QueryKind.signer ∈ Z ∧ QueryKind.sign ∈ Z then 124
      else if QueryKind.signer ∈ Z then 123
      else 122) :=
  Proof.sufCma_exact_of_hash_mem Z hZ

/-- info: 'XmssSecurity.xmss_sufCma_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_sufCma_exact

end XmssSecurity
