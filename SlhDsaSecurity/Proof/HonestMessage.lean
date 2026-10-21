import SlhDsaSecurity.Proof.WotsResidueReduction
import SlhDsaSecurity.Proof.GraphStakes

/-!
# The message a hypertree key signs, as a function of the key

`GraphStakes.honestMessage` is *defined* as the honest node one layer down, read off the key's
own coordinates. That definition is only worth something if it is the message the hypertree
actually threads into that key, and this file proves it, against
`WotsResidueReduction.revealedAt` — the recursion the residue reduction itself produces.

The content is one piece of index arithmetic. The residue threads, as the message for the key
reached after `i + 1` steps, the honest node of the subtree the previous step was looking at;
that subtree's coordinates are `(layerAt layer i, treeAt tree i)`. The key reached after `i + 1`
steps sits at layer `layerAt layer (i + 1)` with subtree index `treeAt tree (i + 1)` and leaf
`leafAt leaf tree (i + 1)`, and those two recombine to the previous subtree index exactly:
dividing by `2 ^ subtreeHeight` and taking the remainder is what the step does, so putting them
back together is `Nat.div_add_mod`.

So the message is a function of the key and the seeds alone, which is what the whole WOTS clause
rests on — each hypertree key signs one message, fixed before the adversary runs.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.HonestMessage

open CanonicalGraph WotsResidueReduction

/-- **The step's subtree index and leaf recombine to the subtree the step came from.** -/
theorem treeAt_succ_add_leafAt (tree : Nat) :
    ∀ (i : Nat) (leaf : SlhDsaSecurity.Hypertree.LeafIndex),
      treeAt tree (i + 1) * 2 ^ subtreeHeight + (leafAt leaf tree (i + 1)).val =
        treeAt tree i := by
  intro i
  induction i generalizing tree with
  | zero =>
    intro leaf
    show tree / 2 ^ subtreeHeight * 2 ^ subtreeHeight + tree % 2 ^ subtreeHeight = tree
    rw [Nat.mul_comm]
    exact Nat.div_add_mod tree (2 ^ subtreeHeight)
  | succ i ih =>
    intro leaf
    exact ih (tree / 2 ^ subtreeHeight) (SlhDsaSecurity.Hypertree.nextLeaf tree)

attribute [local irreducible] Extraction.HypertreeChain.honestNode CanonicalGraph.value

variable [HasQuery HashSpec Id]

/-- **The message the residue threads at step `i + 1`** is the honest node of the subtree the
previous step was looking at. -/
theorem revealedAt_succ (secretSeed publicSeed : Digest) :
    ∀ (i : Nat) (expectedInput : Digest) (layer tree : Nat),
      revealedAt secretSeed publicSeed expectedInput layer tree (i + 1) =
        Extraction.HypertreeChain.honestNode secretSeed publicSeed (layerAt layer i)
          (treeAt tree i) := by
  intro i
  induction i with
  | zero =>
    intro expectedInput layer tree
    simp only [revealedAt, layerAt, treeAt]
  | succ i ih =>
    intro expectedInput layer tree
    rw [show revealedAt secretSeed publicSeed expectedInput layer tree (i + 1 + 1) =
        revealedAt secretSeed publicSeed
          (Extraction.HypertreeChain.honestNode secretSeed publicSeed layer tree) (layer + 1)
          (tree / 2 ^ subtreeHeight) (i + 1) from rfl,
      ih _ (layer + 1) (tree / 2 ^ subtreeHeight)]
    simp only [layerAt, treeAt]

/-- Above the bottom layer, the message a key signs is the honest node of the subtree its own
coordinates name. -/
theorem honestMessage_succ (secretSeed publicSeed : Digest) (key : WotsKey) (layer : Nat)
    (hlayer : key.tree.layer.val = layer + 1) :
    GraphStakes.honestMessage secretSeed publicSeed key =
      Extraction.HypertreeChain.honestNode secretSeed publicSeed layer
        (key.tree.tree.val * 2 ^ subtreeHeight + key.leaf.val) := by
  rw [GraphStakes.honestMessage, hlayer]

/-- **The message the residue threads is the message the key signs.** -/
theorem honestMessage_eq_revealedAt (secretSeed publicSeed expectedInput : Digest)
    (layer tree : Nat) (leaf : SlhDsaSecurity.Hypertree.LeafIndex) (i : Nat) (key : WotsKey)
    (hlayer : key.tree.layer.val = layerAt layer (i + 1))
    (htree : key.tree.tree.val = treeAt tree (i + 1))
    (hleaf : key.leaf.val = (leafAt leaf tree (i + 1)).val) :
    GraphStakes.honestMessage secretSeed publicSeed key =
      revealedAt secretSeed publicSeed expectedInput layer tree (i + 1) := by
  rw [honestMessage_succ secretSeed publicSeed key (layerAt layer i) (by
      rw [hlayer, layerAt_eq, layerAt_eq]; omega),
    revealedAt_succ secretSeed publicSeed i expectedInput layer tree, htree, hleaf,
    treeAt_succ_add_leafAt tree i leaf]

/-- **The revealed digit is the digit of the message the residue threads.** The instantiation
the WOTS clause asks for: `GraphStakes.honestRevealed` really is the digit that key's own
signature discloses. -/
theorem honestRevealed_eq (secretSeed publicSeed expectedInput : Digest)
    (layer tree : Nat) (leaf : SlhDsaSecurity.Hypertree.LeafIndex) (i : Nat) (key : WotsKey)
    (hlayer : key.tree.layer.val = layerAt layer (i + 1))
    (htree : key.tree.tree.val = treeAt tree (i + 1))
    (hleaf : key.leaf.val = (leafAt leaf tree (i + 1)).val) (chain : Fin chains) :
    GraphStakes.honestRevealed secretSeed publicSeed key chain =
      (Checksum.encode (revealedAt secretSeed publicSeed expectedInput layer tree (i + 1))
        chain).val := by
  rw [GraphStakes.honestRevealed,
    honestMessage_eq_revealedAt secretSeed publicSeed expectedInput layer tree leaf i key
      hlayer htree hleaf]

/-! ## The signer's own threading

Tying the revealed digit to the *fault*'s threading is not enough, and the slack is fatal in
both directions: a digit larger than the signer's makes availability too generous, so a forgery
could rest on a cell declared available and fall outside the charged event; a digit smaller than
the signer's makes it too mean, so a query at a cell the signer really did disclose counts as
sensitive and the rate is simply false. So the digit has to be the signer's exactly.

It is. The honest signer's `step`-th layer signs the message the extraction threads at that
step, with the key at the coordinates the accumulators name — `Correctness.Merkle` supplies the
one fact the induction needs, that an honest subtree's recovered root is its honest node. -/

/-- **The honest signer's `step`-th layer signs the threaded message, at the threaded key.** -/
theorem signLayers_get (secretSeed publicSeed : Digest) :
    ∀ (remaining layer tree : Nat) (leaf : SlhDsaSecurity.Hypertree.LeafIndex)
      (message : Digest) (step : Fin (remaining + 1)),
      (SlhDsaSecurity.Hypertree.signLayers (m := Id) secretSeed publicSeed (remaining + 1)
        layer tree leaf message) step =
        SlhDsaSecurity.Merkle.sign (m := Id)
          (revealedAt secretSeed publicSeed message layer tree step.val)
          secretSeed publicSeed
          (SlhDsaSecurity.Hypertree.address (layerAt layer step.val) (treeAt tree step.val))
          (leafAt leaf tree step.val) := by
  intro remaining
  induction remaining with
  | zero =>
    intro layer tree leaf message step
    rw [SlhDsaSecurity.Hypertree.signLayers]
    simp only [bind, pure]
    induction step using Fin.cases with
    | zero => simp only [Fin.cases_zero, revealedAt, layerAt, treeAt, leafAt]
    | succ j => exact j.elim0
  | succ remaining ih =>
    intro layer tree leaf message step
    rw [SlhDsaSecurity.Hypertree.signLayers]
    simp only [bind, pure]
    induction step using Fin.cases with
    | zero => simp only [Fin.cases_zero, Fin.val_zero, revealedAt, layerAt, treeAt, leafAt]
    | succ j =>
      simp only [Fin.cases_succ]
      rw [Correctness.Merkle.publicKeyFromSignature_sign,
        ih (layer + 1) (tree / 2 ^ subtreeHeight) (SlhDsaSecurity.Hypertree.nextLeaf tree)
          ((SlhDsaSecurity.Merkle.node (m := Id) secretSeed publicSeed
            (SlhDsaSecurity.Hypertree.address layer tree) subtreeHeight 0 : Digest)) j]
      simp only [Fin.val_succ, revealedAt, Extraction.HypertreeChain.honestNode, layerAt, treeAt,
        leafAt]

/-- **So the honest signer's WOTS signature at that layer is on the key's own message.** The
digit `GraphStakes.honestRevealed` names is the digit the signer really discloses. -/
theorem signLayers_wots (secretSeed publicSeed : Digest) (remaining layer tree : Nat)
    (leaf : SlhDsaSecurity.Hypertree.LeafIndex) (message : Digest) (i : Nat)
    (step : Fin (remaining + 1)) (hstep : step.val = i + 1) (key : WotsKey)
    (hlayer : key.tree.layer.val = layerAt layer step.val)
    (htree : key.tree.tree.val = treeAt tree step.val)
    (hleaf : key.leaf.val = (leafAt leaf tree step.val).val) :
    ((SlhDsaSecurity.Hypertree.signLayers (m := Id) secretSeed publicSeed (remaining + 1)
        layer tree leaf message) step).wots =
      SlhDsaSecurity.Wots.sign (m := Id)
        (GraphStakes.honestMessage secretSeed publicSeed key) secretSeed publicSeed
        key.address := by
  rw [signLayers_get secretSeed publicSeed remaining layer tree leaf message step,
    honestMessage_eq_revealedAt secretSeed publicSeed message layer tree leaf i key
      (by rw [hlayer, hstep]) (by rw [htree, hstep]) (by rw [hleaf, hstep]), ← hstep]
  show SlhDsaSecurity.Wots.sign (m := Id) _ secretSeed publicSeed
      (SlhDsaSecurity.Merkle.wotsAddress
        (SlhDsaSecurity.Hypertree.address (layerAt layer step.val) (treeAt tree step.val))
        (leafAt leaf tree step.val).val) = _
  rw [WotsKey.address, Tree.address, hlayer, htree, hleaf]

end SlhDsaSecurity.HonestMessage
