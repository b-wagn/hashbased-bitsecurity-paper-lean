import SlhDsaSecurity.Statement.Hypertree
import SlhDsaSecurity.Proof.Correctness.Merkle

/-! Correctness of all seven actual hypertree layers under any fixed hash. -/

open OracleComp OracleSpec

namespace SlhDsaSecurity.Correctness.Hypertree

variable [HasQuery HashSpec Id]

theorem rootFromSignature_signLayers (secretSeed publicSeed : Digest)
    (remaining layer tree : Nat) (leaf : SlhDsaSecurity.Hypertree.LeafIndex)
    (message : Digest) :
    SlhDsaSecurity.Hypertree.rootFromSignature (m := Id) publicSeed (remaining + 1)
        (SlhDsaSecurity.Hypertree.signLayers (m := Id) secretSeed publicSeed
          (remaining + 1) layer tree leaf message)
        layer tree leaf message =
      SlhDsaSecurity.Merkle.node (m := Id) secretSeed publicSeed
        (SlhDsaSecurity.Hypertree.address (layer + remaining)
          (tree / 2 ^ (subtreeHeight * remaining))) subtreeHeight 0 := by
  induction remaining generalizing layer tree leaf message with
  | zero =>
      simp only [SlhDsaSecurity.Hypertree.signLayers,
        SlhDsaSecurity.Hypertree.rootFromSignature, bind, pure, Fin.cases_zero,
        Merkle.publicKeyFromSignature_sign, Nat.add_zero, Nat.mul_zero, pow_zero,
        Nat.div_one]
  | succ remaining ih =>
      rw [SlhDsaSecurity.Hypertree.signLayers]
      simp only [bind, pure]
      rw [SlhDsaSecurity.Hypertree.rootFromSignature]
      simp only [bind, Fin.cases_zero, Fin.cases_succ]
      rw [Merkle.publicKeyFromSignature_sign, ih]
      have hlayer : layer + 1 + remaining = layer + (remaining + 1) := by omega
      have hexponent : subtreeHeight + subtreeHeight * remaining =
          subtreeHeight * (remaining + 1) := by
        simp only [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      rw [hlayer, Nat.div_div_eq_div_mul, ← pow_add, hexponent]

theorem rootFromSignature_sign (message secretSeed publicSeed : Digest)
    (tree : SlhDsaSecurity.Hypertree.TreeIndex)
    (leaf : SlhDsaSecurity.Hypertree.LeafIndex) :
    SlhDsaSecurity.Hypertree.rootFromSignature (m := Id) publicSeed layers
        (SlhDsaSecurity.Hypertree.sign (m := Id) message secretSeed publicSeed tree leaf)
        0 tree.toNat leaf message =
      SlhDsaSecurity.Merkle.node (m := Id) secretSeed publicSeed
        (SlhDsaSecurity.Hypertree.address (layers - 1) 0) subtreeHeight 0 := by
  have htree : tree.toNat < 2 ^ (subtreeHeight * (layers - 1)) := by
    exact tree.isLt
  have h := rootFromSignature_signLayers secretSeed publicSeed (layers - 1) 0 tree.toNat leaf message
  rw [Nat.zero_add, Nat.div_eq_of_lt htree] at h
  exact h

theorem verify_sign (message secretSeed : Digest) (pk : PublicKey)
    (tree : SlhDsaSecurity.Hypertree.TreeIndex)
    (leaf : SlhDsaSecurity.Hypertree.LeafIndex)
    (hroot : pk.root = SlhDsaSecurity.Merkle.node (m := Id) secretSeed pk.seed
      (SlhDsaSecurity.Hypertree.address (layers - 1) 0) subtreeHeight 0) :
    SlhDsaSecurity.Hypertree.verify (m := Id) message
        (SlhDsaSecurity.Hypertree.sign (m := Id) message secretSeed pk.seed tree leaf)
        pk tree leaf = true := by
  simp only [SlhDsaSecurity.Hypertree.verify, rootFromSignature_sign, bind, pure, ← hroot,
    beq_self_eq_true]

end SlhDsaSecurity.Correctness.Hypertree
