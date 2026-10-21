import SlhDsaSecurity.Proof.Extraction.HypertreeChain
import SlhDsaSecurity.Proof.CacheReplay

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

open OracleComp OracleSpec

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

/-! ## The top of the structural chain

Composing the seven-layer soundness theorem with the flattening gives the statement the
charge consumes directly: an accepted hypertree signature either carries the genuine FORS
public key — in which case the forgery has to be explained on the FORS side, which is the
business of `Extraction.Fors` — or it exhibits one of the two faults, and each of those is
charged.

Nothing in this step is probabilistic. It is the whole structural reduction of SLH-DSA
verification to events a random oracle can be charged for, with no assumption of collision
resistance or one-wayness anywhere: both are *conclusions* about the adversary's queries, not
hypotheses about the hash. -/

/-- **An accepted hypertree signature is canonical or faulty.** -/
theorem cases_of_accepted (secretSeed publicSeed : Digest) (pk : PublicKey)
    (tree : SlhDsaSecurity.Hypertree.TreeIndex) (leaf : SlhDsaSecurity.Hypertree.LeafIndex)
    (forsKey honestForsKey : Digest) (signature : HypertreeSignature)
    (hseed : pk.seed = publicSeed)
    (hroot : pk.root = honestNode secretSeed publicSeed (layers - 1) 0)
    (haccept : SlhDsaSecurity.Hypertree.verify (m := Id) forsKey signature pk tree leaf = true) :
    forsKey = honestForsKey ∨
      SomeLayerCollision secretSeed publicSeed ∨ SomeWotsWitness secretSeed publicSeed := by
  rcases verify_fault_or_fors_canonical secretSeed publicSeed pk tree leaf forsKey honestForsKey
    signature hseed hroot haccept with hcanonical | hfault
  · exact Or.inl hcanonical
  · exact Or.inr (cases_of_hypertreeFault secretSeed publicSeed layers signature 0 tree.toNat
      leaf forsKey honestForsKey hfault)

/-! ## Walking down the layers

`Hypertree.rootFromSignature` is a recursion, one `Merkle.publicKeyFromSignature` per layer,
each fed the root the layer below produced. A collision sits at one particular layer, so
reaching its query means walking down to that layer — and the two directions of
`CacheReplay.queriesUnder_bind` and `queriesUnder_bind_right` are exactly the two steps of
that walk: descend into this layer, or step over it to the next.

Stepping over a layer advances the message to that layer's replayed root, which is what
`CacheReplay.run_eq_replay` identifies with the root the oracle run actually produced. -/

open CacheReplay in
/-- Descend into this layer. -/
theorem queriesUnder_rootFromSignature_head (cache : QueryCache HashSpec) (publicSeed : Digest)
    (remaining : Nat) (signatures : Fin (remaining + 1) → XmssSignature) (layer tree : Nat)
    (leaf : SlhDsaSecurity.Hypertree.LeafIndex) (message : Digest) (probe : Bytes)
    (hquery : QueriesUnder cache
      (SlhDsaSecurity.Merkle.publicKeyFromSignature (m := OracleComp HashSpec) leaf
        (signatures 0) message publicSeed (SlhDsaSecurity.Hypertree.address layer tree)) probe) :
    QueriesUnder cache
      (SlhDsaSecurity.Hypertree.rootFromSignature (m := OracleComp HashSpec) publicSeed
        (remaining + 1) signatures layer tree leaf message) probe :=
  queriesUnder_bind cache _ _ probe hquery

open CacheReplay in
/-- Step over this layer to the next, advancing the message to this layer's replayed root. -/
theorem queriesUnder_rootFromSignature_tail (cache : QueryCache HashSpec) (publicSeed : Digest)
    (remaining : Nat) (signatures : Fin (remaining + 1) → XmssSignature) (layer tree : Nat)
    (leaf : SlhDsaSecurity.Hypertree.LeafIndex) (message : Digest) (probe : Bytes)
    (hquery : QueriesUnder cache
      (SlhDsaSecurity.Hypertree.rootFromSignature (m := OracleComp HashSpec) publicSeed
        remaining (fun i => signatures i.succ) (layer + 1)
        (tree / 2 ^ subtreeHeight) (SlhDsaSecurity.Hypertree.nextLeaf tree)
        (simulateQ (replay cache)
          (SlhDsaSecurity.Merkle.publicKeyFromSignature (m := OracleComp HashSpec) leaf
            (signatures 0) message publicSeed
            (SlhDsaSecurity.Hypertree.address layer tree)))) probe) :
    QueriesUnder cache
      (SlhDsaSecurity.Hypertree.rootFromSignature (m := OracleComp HashSpec) publicSeed
        (remaining + 1) signatures layer tree leaf message) probe :=
  queriesUnder_bind_right cache _ _ probe hquery

end SlhDsaSecurity.HypertreeDispatch
