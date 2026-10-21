import SlhDsaSecurity.Proof.Extraction.HypertreeChain

/-!
# Unfolding the seven-layer fault

`Extraction.HypertreeChain.HypertreeFault` is a recursion down the hypertree: at each layer
either the layer itself collides, or that layer's WOTS signature is the honest signature of a
message differing from the honest input threaded into it, or the fault lies further up. The
recursion is how the extraction chain is proved; what the charge needs is the flattened form —
*some* layer collides, or *some* layer carries a WOTS signature for the wrong message.

The two cases land on different sides of the security budget, which is why they are kept
apart rather than merged. A layer collision is a structural event: a query whose answer hits
an honest cell, charged at `2 ^ -128` on the structural class. A WOTS signature for a message
the honest chain never signed is a one-wayness witness — the adversary holds chain values
below what any signature revealed — and that is a secret-side event, charged on the input
half of the budget.
-/

namespace SlhDsaSecurity.HypertreeDispatch

open Extraction.HypertreeChain

variable [HasQuery HashSpec Id]

/-- A layer collision somewhere in the segment. -/
def SomeLayerCollision (secretSeed publicSeed : Digest) : Prop :=
  ∃ (message : Digest) (layer tree : Nat) (leaf : SlhDsaSecurity.Hypertree.LeafIndex)
    (signature : XmssSignature),
    Extraction.Hypertree.LayerCollision secretSeed publicSeed message layer tree leaf signature

/-- A layer whose WOTS signature is the honest signature of the wrong message. -/
def SomeWotsWitness (secretSeed publicSeed : Digest) : Prop :=
  ∃ (message expected : Digest) (layer tree : Nat)
    (leaf : SlhDsaSecurity.Hypertree.LeafIndex) (signature : XmssSignature),
    signature.wots = SlhDsaSecurity.Wots.sign (m := Id) message secretSeed publicSeed
        (Extraction.Hypertree.wotsAddress layer tree leaf) ∧ message ≠ expected

/-- **The seven-layer fault flattens to one of the two cases.** -/
theorem cases_of_hypertreeFault (secretSeed publicSeed : Digest) :
    ∀ (remaining : Nat) (signatures : Fin remaining → XmssSignature) (layer tree : Nat)
      (leaf : SlhDsaSecurity.Hypertree.LeafIndex) (message expectedInput : Digest),
      HypertreeFault secretSeed publicSeed remaining signatures layer tree leaf message
        expectedInput →
        SomeLayerCollision secretSeed publicSeed ∨ SomeWotsWitness secretSeed publicSeed := by
  intro remaining
  induction remaining with
  | zero => intro _ _ _ _ _ _ hfault; exact hfault.elim
  | succ remaining ih =>
    intro signatures layer tree leaf message expectedInput hfault
    unfold HypertreeFault at hfault
    rcases hfault with hcollision | hwitness | hrest
    · exact Or.inl ⟨message, layer, tree, leaf, signatures 0, hcollision⟩
    · exact Or.inr ⟨message, expectedInput, layer, tree, leaf, signatures 0,
        hwitness.1, hwitness.2⟩
    · exact ih _ _ _ _ _ _ hrest

end SlhDsaSecurity.HypertreeDispatch
