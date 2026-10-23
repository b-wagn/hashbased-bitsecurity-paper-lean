import «SLH-DSA-SHAKE-128s».Statement.Wots

/-! FIPS 205 Algorithms 9–11: one height-nine XMSS subtree of the SLH-DSA hypertree. -/

open OracleComp OracleSpec

namespace SlhDsaSecurity.Merkle

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

def wotsAddress (address : Address) (index : Nat) : Address :=
  { address.setTypeAndClear .wotsHash with keyPair := BitVec.ofNat 32 index }

def nodeAddress (address : Address) (height index : Nat) : Address :=
  { address.setTypeAndClear .tree with
    chainOrHeight := BitVec.ofNat 32 height, hashOrIndex := BitVec.ofNat 32 index }

/-- Algorithm 9, evaluating the left child before the right child. -/
def node (secretSeed publicSeed : Digest) (address : Address) :
    Nat → Nat → m Digest
  | 0, index => Wots.publicKey secretSeed publicSeed (wotsAddress address index)
  | height + 1, index => do
    let left ← node secretSeed publicSeed address height (2 * index)
    let right ← node secretSeed publicSeed address height (2 * index + 1)
    Hashing.tweakable publicSeed (nodeAddress address (height + 1) index)
      (bytesBE n left ++ bytesBE n right)

/-- Algorithm 10 computes the authentication path first, then the WOTS signature. -/
def sign (message secretSeed publicSeed : Digest) (address : Address)
    (index : Fin (2 ^ subtreeHeight)) : m XmssSignature := do
  let authentication ← sequenceFin subtreeHeight fun j =>
    node secretSeed publicSeed address j.val (Nat.xor (index.val / 2 ^ j.val) 1)
  let wots ← Wots.sign message secretSeed publicSeed (wotsAddress address index.val)
  return { wots, authentication }

/-- Algorithm 11: recover the WOTS key, then climb through all nine authentication nodes. -/
def publicKeyFromSignature (index : Fin (2 ^ subtreeHeight)) (signature : XmssSignature)
    (message publicSeed : Digest) (address : Address) : m Digest := do
  let leaf ← Wots.publicKeyFromSignature signature.wots message publicSeed
    (wotsAddress address index.val)
  (List.finRange subtreeHeight).foldlM (fun value j => do
    let payload := if index.val / 2 ^ j.val % 2 = 0 then
      bytesBE n value ++ bytesBE n (signature.authentication j)
      else bytesBE n (signature.authentication j) ++ bytesBE n value
    Hashing.tweakable publicSeed
      (nodeAddress address (j.val + 1) (index.val / 2 ^ (j.val + 1))) payload) leaf

end SlhDsaSecurity.Merkle
