import «SLH-DSA-128s».Statement.Checksum
import «SLH-DSA-128s».Statement.Hashing
import «SLH-DSA-128s».Statement.Signature

/-! FIPS 205 Algorithms 5–8: WOTS+ with the standard 35 chains of length 16. -/

open OracleComp OracleSpec

namespace SlhDsaSecurity.Wots

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- Algorithm 5. Hash addresses run from `start` through `start + steps - 1`. -/
def chain (publicSeed : Digest) (address : Address) :
    Nat → Nat → Digest → m Digest
  | _, 0, value => pure value
  | start, steps + 1, value => do
    let next ← Hashing.tweakable publicSeed
      { address with hashOrIndex := BitVec.ofNat 32 start } (bytesBE n value)
    chain publicSeed address (start + 1) steps next

/-- WOTS_PRF clears the hash word and preserves this WOTS key's address. -/
def secretAddress (address : Address) (chainIndex : Fin chains) : Address :=
  { address.setTypeAndClear .wotsPrf with
    keyPair := address.keyPair, chainOrHeight := BitVec.ofNat 32 chainIndex.val }

def publicKeyAddress (address : Address) : Address :=
  { address.setTypeAndClear .wotsPk with keyPair := address.keyPair }

/-- Algorithm 6: derive each secret on demand, finish its chain, then compress. -/
def publicKey (secretSeed publicSeed : Digest) (address : Address) : m Digest := do
  let endpoints ← sequenceFin chains fun i => do
    let secret ← Hashing.derive publicSeed secretSeed (secretAddress address i)
    chain publicSeed { address with chainOrHeight := BitVec.ofNat 32 i.val }
      0 (w - 1) secret
  Hashing.tweakable publicSeed (publicKeyAddress address) (digestArrayBytes endpoints)

/-- Algorithm 7, using the standard checksum digits. -/
def sign (message secretSeed publicSeed : Digest) (address : Address) : m WotsSignature :=
  sequenceFin chains fun i => do
    let secret ← Hashing.derive publicSeed secretSeed (secretAddress address i)
    chain publicSeed { address with chainOrHeight := BitVec.ofNat 32 i.val }
      0 (Checksum.encode message i).val secret

/-- Algorithm 8. Even repeated hash inputs are queried again. -/
def publicKeyFromSignature (signature : WotsSignature) (message publicSeed : Digest)
    (address : Address) : m Digest := do
  let endpoints ← sequenceFin chains fun i =>
    let digit := (Checksum.encode message i).val
    chain publicSeed { address with chainOrHeight := BitVec.ofNat 32 i.val }
      digit (w - 1 - digit) (signature i)
  Hashing.tweakable publicSeed (publicKeyAddress address) (digestArrayBytes endpoints)

end SlhDsaSecurity.Wots
