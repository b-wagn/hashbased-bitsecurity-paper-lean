import SlhDsaSecurity.Statement.Hashing
import SlhDsaSecurity.Statement.MessageDigest
import SlhDsaSecurity.Statement.Signature

/-! FIPS 205 Algorithms 14–17: fourteen FORS trees, each with 4096 leaves. -/

open OracleComp OracleSpec

namespace SlhDsaSecurity.Fors

abbrev Indices := MessageDigest.ForsTree → MessageDigest.ForsLeaf

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

def secretAddress (address : Address) (index : Nat) : Address :=
  { address.setTypeAndClear .forsPrf with
    keyPair := address.keyPair, hashOrIndex := BitVec.ofNat 32 index }

def nodeAddress (address : Address) (height index : Nat) : Address :=
  { address with
    chainOrHeight := BitVec.ofNat 32 height, hashOrIndex := BitVec.ofNat 32 index }

/-- Algorithm 14. The index includes the offset of this FORS tree. -/
def secret (secretSeed publicSeed : Digest) (address : Address) (index : Nat) : m Digest :=
  Hashing.derive publicSeed secretSeed (secretAddress address index)

/-- Algorithm 15. Nodes use the global index across all fourteen FORS trees. -/
def node (secretSeed publicSeed : Digest) (address : Address) :
    Nat → Nat → m Digest
  | 0, index => do
    let value ← secret secretSeed publicSeed address index
    Hashing.tweakable publicSeed (nodeAddress address 0 index) (bytesBE n value)
  | height + 1, index => do
    let left ← node secretSeed publicSeed address height (2 * index)
    let right ← node secretSeed publicSeed address height (2 * index + 1)
    Hashing.tweakable publicSeed (nodeAddress address (height + 1) index)
      (bytesBE n left ++ bytesBE n right)

/-- Algorithm 16: each selected secret is followed by its authentication path. -/
def sign (indices : Indices) (secretSeed publicSeed : Digest) (address : Address) :
    m ForsSignature :=
  sequenceFin forsTrees fun i => do
    let selected ← secret secretSeed publicSeed address
      (i.val * 2 ^ forsHeight + (indices i).val)
    let authentication ← sequenceFin forsHeight fun j =>
      node secretSeed publicSeed address j.val
        (i.val * 2 ^ (forsHeight - j.val) + Nat.xor ((indices i).val / 2 ^ j.val) 1)
    return { secret := selected, authentication }

/-- Algorithm 17: authenticate the fourteen leaves and compress their roots. -/
def publicKeyFromSignature (signature : ForsSignature) (indices : Indices)
    (publicSeed : Digest) (address : Address) : m Digest := do
  let roots ← sequenceFin forsTrees fun i => do
    let index := i.val * 2 ^ forsHeight + (indices i).val
    let leaf ← Hashing.tweakable publicSeed (nodeAddress address 0 index)
      (bytesBE n (signature i).secret)
    (List.finRange forsHeight).foldlM (fun value j => do
      let payload := if (indices i).val / 2 ^ j.val % 2 = 0 then
        bytesBE n value ++ bytesBE n ((signature i).authentication j)
        else bytesBE n ((signature i).authentication j) ++ bytesBE n value
      Hashing.tweakable publicSeed
        (nodeAddress address (j.val + 1) (index / 2 ^ (j.val + 1))) payload) leaf
  let rootAddress := { address.setTypeAndClear .forsRoots with keyPair := address.keyPair }
  Hashing.tweakable publicSeed rootAddress (digestArrayBytes roots)

end SlhDsaSecurity.Fors
