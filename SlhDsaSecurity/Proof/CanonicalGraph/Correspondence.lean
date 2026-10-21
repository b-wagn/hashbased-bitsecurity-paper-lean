import SlhDsaSecurity.Proof.CanonicalGraph.Evaluation
import SlhDsaSecurity.Proof.Correctness.Fors
import SlhDsaSecurity.Proof.Correctness.Hypertree

/-! Honest signatures disclose canonical cells; messages only select their positions. -/

open OracleComp OracleSpec

namespace SlhDsaSecurity.CanonicalGraph

/-- Position zero is the PRF-derived secret; position fifteen is the chain endpoint. -/
def wotsPosition (key : WotsKey) (chain : Fin chains) (position : Fin w) : StructuralNode :=
  if hzero : position.val = 0 then .wotsPrf key chain
  else .wotsHash key chain ⟨position.val - 1, by have := position.isLt; omega⟩

def topRoot : StructuralNode :=
  .tree ⟨⟨layers - 1, by decide⟩, ⟨0, by decide⟩⟩
    ⟨subtreeHeight - 1, by decide⟩ ⟨0, by decide⟩

variable [HasQuery HashSpec Id]

theorem value_wotsPosition (secretSeed publicSeed : Digest) (key : WotsKey)
    (chain : Fin chains) (position : Fin w) :
    value secretSeed publicSeed (.structural (wotsPosition key chain position)) =
      Wots.chain (m := Id) publicSeed
        { key.address with chainOrHeight := BitVec.ofNat 32 chain.val } 0 position.val
        (Hashing.derive (m := Id) publicSeed secretSeed (Wots.secretAddress key.address chain)) := by
  unfold wotsPosition
  split
  · rename_i hzero
    simp only [value, structuralValue, hzero, Wots.chain, pure]
  · rename_i hzero
    simp only [value, structuralValue]
    rw [Nat.sub_add_cancel (by omega : 1 ≤ position.val)]

theorem wots_sign_cells (message secretSeed publicSeed : Digest) (key : WotsKey) :
    Wots.sign (m := Id) message secretSeed publicSeed key.address =
      fun chain => value secretSeed publicSeed
        (.structural (wotsPosition key chain (Checksum.encode message chain))) := by
  simp only [Wots.sign, Correctness.sequenceFin_id, bind]
  funext chain
  exact (value_wotsPosition _ _ _ _ _).symm

theorem wots_publicKey_cell (secretSeed publicSeed : Digest) (key : WotsKey) :
    Wots.publicKey (m := Id) secretSeed publicSeed key.address =
      value secretSeed publicSeed (.structural (.wotsPk key)) := rfl

theorem fors_secret_cell (secretSeed publicSeed : Digest) (key : ForsKey)
    (index : Fin (forsTrees * 2 ^ forsHeight)) :
    Fors.secret (m := Id) secretSeed publicSeed key.address index.val =
      value secretSeed publicSeed (.structural (.forsPrf key index)) := rfl

/-- Every selected FORS message authenticates the same canonical collection of roots. -/
theorem fors_publicKey_cell (indices : Fors.Indices) (secretSeed publicSeed : Digest)
    (key : ForsKey) :
    Fors.publicKeyFromSignature (m := Id)
        (Fors.sign (m := Id) indices secretSeed publicSeed key.address)
        indices publicSeed key.address =
      value secretSeed publicSeed (.structural (.forsRoots key)) :=
  Correctness.Fors.publicKeyFromSignature_sign _ _ _ _

theorem keygen_root_cell (secretSeed prfSeed publicSeed : Digest) :
    (Scheme.keygenInternal (m := Id) secretSeed prfSeed publicSeed).2.root =
      value secretSeed publicSeed (.structural topRoot) := rfl

theorem hypertree_root_cell (message secretSeed publicSeed : Digest)
    (tree : Hypertree.TreeIndex) (leaf : Hypertree.LeafIndex) :
    Hypertree.rootFromSignature (m := Id) publicSeed layers
        (Hypertree.sign (m := Id) message secretSeed publicSeed tree leaf)
        0 tree.toNat leaf message =
      value secretSeed publicSeed (.structural topRoot) :=
  Correctness.Hypertree.rootFromSignature_sign _ _ _ _ _

end SlhDsaSecurity.CanonicalGraph
