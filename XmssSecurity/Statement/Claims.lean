import XmssSecurity.Statement.Scheme.Xmss

/-!
# Security claims about XMSS

The bit-security statements of this development: for each of the sixteen counting modes of
SUF-CMA, a lower bound (a security proof) and an upper bound (an attack) on the classical bit
security of XMSS. Each claim is a `Prop` built from the scheme (`Scheme/`), the notion
(`Security/SUFCMA.lean`), and the bit-security definition (`BitSecurity.lean`); the proofs under
`Proof/` only ever change the numbers of bits.

The adversary is probabilistic, adaptive, and has no bound on running time or memory; only its
queries are counted, as the mode specifies. The probability is over the master seed, the random
oracle, and the adversary's private randomness.

## The conjectured picture

The modes form a lattice: charging more queries can only increase `q`, so a security proof for a
mode holds for every mode charging more, and an attack for a mode works for every mode charging
less. The conjecture is that the bit security takes two values:

* 122 bits when only the adversary's own hash calls, and possibly its signing requests, are
  charged (`direct`, and `direct` with `requests`). The attack makes no hash call of its own and
  one signing request, so it is charged at most `1`: it takes the signature and replaces the
  signature value of one chain by a random value. The verifier then hashes the fresh value along
  the rest of that chain, hashes a fresh leaf, and hashes `32` fresh tree nodes; each of these
  `40 - x` fresh hash calls (`x` the chain's digit) hits the corresponding honest value with
  probability `1 / 2^128`, and any such hit makes the forgery verify. Some digit is at most `4`
  (the digits sum to `195` over `42` chains), so the attack succeeds with probability at least
  about `36 / 2^128 > 1 / 2^123`. (Replacing an authentication-path node instead gives at most
  `32` fresh tree hashes, exactly the `1 / 2^123` threshold, so it does not refute 123 bits.)
* 127 bits as soon as the hash calls of key generation, of the signer, or of the final
  verification are charged. Key generation makes about `2^40` hash calls, a signing request up
  to `2^33` (two per randomizer trial, at most `2^32` trials; about `2^16` in expectation), and
  a verification that can succeed makes `133`; so the attack above is charged far more than its
  `40` chances are worth, and without a signature a forgery needs the forged encoding to decode
  (probability about `2^-14.85`) before the verifier's `33` fresh hashes can help. The attack of
  Remark 5.3 ("Why not 128 bits?") of the leanVM XMSS document
  (https://github.com/leanEthereum/leanVM/releases/download/doc-latest/XMSS.pdf) finds, with about `2^121` encoding hashes, a
  second encoding that moves one unit between two digits of a signed encoding, and then a
  preimage of one chain value with about `2^124` hash calls; it succeeds with probability about
  `0.11`, so its work-to-success ratio is about `2^127.3`, and the honest parties' calls do not
  change this.
-/

open ENNReal

namespace XmssSecurity

/-- The conjectured classical bit security of XMSS under each counting mode. -/
def conjecturedBits (mode : SUFCMA.CountingMode) : ℕ :=
  if mode.keygen || mode.signer || mode.verifier then 127 else 122

/-- XMSS has `bits` bits of classical SUF-CMA security under `mode`: a security proof. -/
abbrev XmssSufCmaSecure (mode : SUFCMA.CountingMode) (bits : ℕ) : Prop :=
  (SUFCMA.notion mode).HasClassicalSecurityBits xmss bits

/-- XMSS does not have `bits + 1` bits of classical SUF-CMA security under `mode`: an attack. -/
abbrev XmssSufCmaAttack (mode : SUFCMA.CountingMode) (bits : ℕ) : Prop :=
  ¬ (SUFCMA.notion mode).HasClassicalSecurityBits xmss (bits + 1)

/-- The complete picture: under every counting mode, XMSS has exactly the conjectured number of
bits of classical SUF-CMA security. -/
abbrev XmssSufCmaExactStatement : Prop :=
  ∀ mode : SUFCMA.CountingMode,
    (SUFCMA.notion mode).HasExactClassicalSecurityBits xmss (conjecturedBits mode)

/-! ### Milestones

Claims proved so far, or under proof, towards `XmssSufCmaExactStatement`. -/

/-- XMSS has 127 bits of classical SUF-CMA security, counting every hash call of the experiment
(key generation, the adversary, the signer, and the verification of the forgery). -/
abbrev XmssSufCmaAllHashesStatement : Prop :=
  XmssSufCmaSecure SUFCMA.CountingMode.allHashes 127

/-- XMSS has 119 bits of classical SUF-CMA security, counting only the adversary's own hash
calls. The level is what the current proof gives; the conjectured level is 122 (the proof
charges the forgery's verification and a constant number of probes at full weight, which costs
3 bits at the smallest query budgets). -/
abbrev XmssSufCmaDirectStatement : Prop :=
  XmssSufCmaSecure SUFCMA.CountingMode.direct 119

/-- Counting only the adversary's own hash calls, XMSS does not have 123 bits of classical
SUF-CMA security. -/
abbrev XmssSufCmaDirectAttackStatement : Prop :=
  XmssSufCmaAttack SUFCMA.CountingMode.direct 122

/-- Counting every hash call and every signing request, XMSS does not have 128 bits of classical
SUF-CMA security. -/
abbrev XmssSufCmaEverythingAttackStatement : Prop :=
  XmssSufCmaAttack SUFCMA.CountingMode.everything 127

end XmssSecurity
