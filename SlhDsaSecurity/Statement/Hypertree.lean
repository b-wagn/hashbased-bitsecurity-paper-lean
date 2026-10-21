import SlhDsaSecurity.Statement.Merkle

/-! FIPS 205 Algorithms 12–13: the seven-layer SLH-DSA-128s hypertree. -/

open OracleComp OracleSpec

namespace SlhDsaSecurity.Hypertree

abbrev LeafIndex := Fin (2 ^ subtreeHeight)
abbrev TreeIndex := BitVec (totalHeight - subtreeHeight)

def address (layer tree : Nat) : Address :=
  { layer := BitVec.ofNat 32 layer, tree := BitVec.ofNat 96 tree }

def nextLeaf (tree : Nat) : LeafIndex :=
  ⟨tree % 2 ^ subtreeHeight, Nat.mod_lt _ (by decide)⟩

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- Algorithm 12's ascending loop. No public-key recovery is done after the last layer. -/
def signLayers (secretSeed publicSeed : Digest) :
    (remaining : Nat) → Nat → Nat → LeafIndex → Digest →
      m (Fin remaining → XmssSignature)
  | 0, _, _, _, _ => pure Fin.elim0
  | remaining + 1, layer, tree, leaf, message => do
    let signature ← Merkle.sign message secretSeed publicSeed (address layer tree) leaf
    match remaining with
    | 0 => return Fin.cases signature Fin.elim0
    | remaining + 1 =>
      let root ← Merkle.publicKeyFromSignature leaf signature message publicSeed
        (address layer tree)
      let rest ← signLayers secretSeed publicSeed (remaining + 1) (layer + 1)
        (tree / 2 ^ subtreeHeight) (nextLeaf tree) root
      return Fin.cases signature rest

def sign (message secretSeed publicSeed : Digest) (tree : TreeIndex) (leaf : LeafIndex) :
    m HypertreeSignature :=
  signLayers secretSeed publicSeed layers 0 tree.toNat leaf message

/-- Algorithm 13's ascending loop, recovering all seven subtree roots. -/
def rootFromSignature (publicSeed : Digest) :
    (remaining : Nat) → (Fin remaining → XmssSignature) → Nat → Nat → LeafIndex → Digest →
      m Digest
  | 0, _, _, _, _, message => pure message
  | remaining + 1, signatures, layer, tree, leaf, message => do
    let root ← Merkle.publicKeyFromSignature leaf (signatures 0) message publicSeed
      (address layer tree)
    rootFromSignature publicSeed remaining (fun i => signatures i.succ) (layer + 1)
      (tree / 2 ^ subtreeHeight) (nextLeaf tree) root

def verify (message : Digest) (signature : HypertreeSignature) (pk : PublicKey)
    (tree : TreeIndex) (leaf : LeafIndex) : m Bool := do
  let root ← rootFromSignature pk.seed layers signature 0 tree.toNat leaf message
  return root == pk.root

end SlhDsaSecurity.Hypertree
