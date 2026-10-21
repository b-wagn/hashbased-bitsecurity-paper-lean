import SlhDsaSecurity.Proof.Extraction.Hypertree
import SlhDsaSecurity.Proof.Extraction.WotsPreimage

/-! Chaining the structural extraction across all hypertree layers.

A forged hypertree signature recovering the honest top root either contains a concrete
structural fault at some layer — a layer collision, or a WOTS signature on a message
differing from the honest input at that layer (which yields a chain preimage witness via
`WotsPreimage.exists_preimage_witness`) — or the bottom layer's incoming message equals
the honest input threaded through every layer. Threaded to the full hypertree, the
fault-free branch forces the recovered FORS public key to equal the honest one, handing
the FORS coverage argument its input. No collision or one-wayness is assumed; every fault
is a concrete witness whose ROM probability is charged in the adaptive assembly. -/

open OracleComp OracleSpec

namespace SlhDsaSecurity.Extraction.HypertreeChain

set_option backward.isDefEq.respectTransparency false

variable [HasQuery HashSpec Id]

/-- The honest root of the subtree at `(layer, tree)` under the genuine seeds. -/
def honestNode (secretSeed publicSeed : Digest) (layer tree : Nat) : Digest :=
  SlhDsaSecurity.Merkle.node (m := Id) secretSeed publicSeed
    (SlhDsaSecurity.Hypertree.address layer tree) subtreeHeight 0

/-- The honest top root reached by folding the given segment upward. The recovered root of
each honest layer is independent of its incoming message, so the fold ignores its input
past the bottom layer. -/
def honestFold (secretSeed publicSeed : Digest) :
    (remaining layer tree : Nat) → Digest → Digest
  | 0, _, _, input => input
  | remaining + 1, layer, tree, _ =>
    honestFold secretSeed publicSeed remaining (layer + 1) (tree / 2 ^ subtreeHeight)
      (honestNode secretSeed publicSeed layer tree)

/-- A concrete structural fault somewhere in the segment: either a layer collision, or a
layer whose WOTS signature is the honest signature of a message differing from the honest
input threaded into that layer. The second case is a WOTS one-wayness witness. -/
def HypertreeFault (secretSeed publicSeed : Digest) :
    (remaining : Nat) → (Fin remaining → XmssSignature) → (layer tree : Nat) →
      SlhDsaSecurity.Hypertree.LeafIndex → (message expectedInput : Digest) → Prop
  | 0, _, _, _, _, _, _ => False
  | remaining + 1, signatures, layer, tree, leaf, message, expectedInput =>
    Extraction.Hypertree.LayerCollision secretSeed publicSeed message layer tree leaf
        (signatures 0) ∨
    ((signatures 0).wots = SlhDsaSecurity.Wots.sign (m := Id) message secretSeed publicSeed
        (Extraction.Hypertree.wotsAddress layer tree leaf) ∧ message ≠ expectedInput) ∨
    HypertreeFault secretSeed publicSeed remaining (fun i => signatures i.succ) (layer + 1)
      (tree / 2 ^ subtreeHeight) (SlhDsaSecurity.Hypertree.nextLeaf tree)
      (SlhDsaSecurity.Merkle.publicKeyFromSignature (m := Id) leaf (signatures 0) message
        publicSeed (SlhDsaSecurity.Hypertree.address layer tree))
      (honestNode secretSeed publicSeed layer tree)

set_option maxRecDepth 10000 in
/-- The seven-layer structural soundness chain. Either a concrete fault occurs at some
layer, or the segment's incoming message equals the honest input threaded through it. -/
theorem rootFromSignature_fault_or_canonical (secretSeed publicSeed rootTarget : Digest)
    (remaining layer tree : Nat) (leaf : SlhDsaSecurity.Hypertree.LeafIndex)
    (message expectedInput : Digest) (signatures : Fin remaining → XmssSignature)
    (htop : SlhDsaSecurity.Hypertree.rootFromSignature (m := Id) publicSeed remaining
        signatures layer tree leaf message = rootTarget)
    (hexp : honestFold secretSeed publicSeed remaining layer tree expectedInput = rootTarget) :
    message = expectedInput ∨
      HypertreeFault secretSeed publicSeed remaining signatures layer tree leaf message
        expectedInput := by
  induction remaining generalizing layer tree leaf message expectedInput with
  | zero =>
    -- No layers: the fold and the recovery both return their input.
    left
    simp only [SlhDsaSecurity.Hypertree.rootFromSignature] at htop
    simp only [honestFold] at hexp
    exact htop.trans hexp.symm
  | succ remaining ih =>
    -- Peel the bottom layer and apply the induction to the upper segment.
    rw [SlhDsaSecurity.Hypertree.rootFromSignature] at htop
    simp only [bind] at htop
    set root₀ := SlhDsaSecurity.Merkle.publicKeyFromSignature (m := Id) leaf (signatures 0)
      message publicSeed (SlhDsaSecurity.Hypertree.address layer tree) with hroot₀
    have hexp' : honestFold secretSeed publicSeed remaining (layer + 1)
        (tree / 2 ^ subtreeHeight) (honestNode secretSeed publicSeed layer tree) = rootTarget := by
      rw [honestFold] at hexp; exact hexp
    rcases ih (layer + 1) (tree / 2 ^ subtreeHeight) (SlhDsaSecurity.Hypertree.nextLeaf tree)
        root₀ (honestNode secretSeed publicSeed layer tree) (fun i => signatures i.succ)
        htop hexp' with hcanon | hfault
    · -- The upper segment recovered the honest node, pinning this layer's output.
      have hbottom : SlhDsaSecurity.Merkle.publicKeyFromSignature (m := Id) leaf (signatures 0)
          message publicSeed (SlhDsaSecurity.Hypertree.address layer tree) =
          SlhDsaSecurity.Merkle.node (m := Id) secretSeed publicSeed
            (SlhDsaSecurity.Hypertree.address layer tree) subtreeHeight 0 := hcanon
      rcases Extraction.Hypertree.layer_canonical_or_collision secretSeed publicSeed message
          layer tree leaf (signatures 0) hbottom with ⟨hwots, _⟩ | hcollision
      · by_cases hmessage : message = expectedInput
        · exact Or.inl hmessage
        · exact Or.inr (Or.inr (Or.inl ⟨hwots, hmessage⟩))
      · exact Or.inr (Or.inl hcollision)
    · exact Or.inr (Or.inr (Or.inr hfault))

/-- The honest fold over `remaining + 1` layers reaches the top subtree root, independent
of its incoming message. Mirrors `Correctness.Hypertree.rootFromSignature_signLayers`. -/
theorem honestFold_eq (secretSeed publicSeed : Digest) (remaining layer tree : Nat)
    (input : Digest) :
    honestFold secretSeed publicSeed (remaining + 1) layer tree input =
      honestNode secretSeed publicSeed (layer + remaining)
        (tree / 2 ^ (subtreeHeight * remaining)) := by
  induction remaining generalizing layer tree input with
  | zero => simp only [honestFold, Nat.add_zero, Nat.mul_zero, pow_zero, Nat.div_one]
  | succ remaining ih =>
    rw [honestFold, ih (layer + 1) (tree / 2 ^ subtreeHeight)
      (honestNode secretSeed publicSeed layer tree)]
    have hlayer : layer + 1 + remaining = layer + (remaining + 1) := by omega
    have hexponent : subtreeHeight + subtreeHeight * remaining =
        subtreeHeight * (remaining + 1) := by ring
    rw [hlayer, Nat.div_div_eq_div_mul, ← pow_add, hexponent]

/-- A forged hypertree signature accepted against an honestly generated key either contains
a concrete structural fault at some layer, or its recovered FORS public key (the bottom
message) equals the honest FORS public key fed into the hypertree. -/
theorem verify_fault_or_fors_canonical (secretSeed publicSeed : Digest) (pk : PublicKey)
    (tree : SlhDsaSecurity.Hypertree.TreeIndex) (leaf : SlhDsaSecurity.Hypertree.LeafIndex)
    (forsKey honestForsKey : Digest) (signature : HypertreeSignature)
    (hseed : pk.seed = publicSeed)
    (hroot : pk.root = honestNode secretSeed publicSeed (layers - 1) 0)
    (haccept : SlhDsaSecurity.Hypertree.verify (m := Id) forsKey signature pk tree leaf = true) :
    forsKey = honestForsKey ∨
      HypertreeFault secretSeed publicSeed layers signature 0 tree.toNat leaf forsKey
        honestForsKey := by
  have htop : SlhDsaSecurity.Hypertree.rootFromSignature (m := Id) publicSeed layers
      signature 0 tree.toNat leaf forsKey = pk.root := by
    rw [← hseed]
    simp only [SlhDsaSecurity.Hypertree.verify, bind, pure] at haccept
    exact (beq_iff_eq (α := Digest)).mp haccept
  have hexp : honestFold secretSeed publicSeed layers 0 tree.toNat honestForsKey = pk.root := by
    have hfold : honestFold secretSeed publicSeed layers 0 tree.toNat honestForsKey =
        honestNode secretSeed publicSeed (layers - 1) 0 := by
      have h := honestFold_eq secretSeed publicSeed (layers - 1) 0 tree.toNat honestForsKey
      have htree : tree.toNat / 2 ^ (subtreeHeight * (layers - 1)) = 0 := by
        apply Nat.div_eq_of_lt
        have := tree.isLt
        simpa only [show totalHeight - subtreeHeight = subtreeHeight * (layers - 1) from rfl] using this
      rw [Nat.zero_add, htree] at h
      exact h
    rw [hfold, hroot]
  exact rootFromSignature_fault_or_canonical secretSeed publicSeed pk.root layers 0 tree.toNat
    leaf forsKey honestForsKey signature htop hexp

end SlhDsaSecurity.Extraction.HypertreeChain
