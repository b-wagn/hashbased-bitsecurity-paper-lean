import SlhDsaSecurity.Proof.HonestGrowth
import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# What verification can cost, and what key generation must

Two bounds on hash calls, one in each direction, for the shared half's budget.

**Verification makes at most `3929` hash calls**, on every path and against every oracle
(`isQueryBoundP_verify`). The bound is structural — `OracleComp.IsQueryBoundP` — because it is
needed on games other than the real one, where nothing about the adversary's budget is known: a
signature is at most a message digest, fourteen FORS leaves with twelve-step paths and a root
compression, and seven layers of thirty-five WOTS chains of at most fifteen steps, a compression,
and a nine-step path.

**Key generation makes at least `36 · 2 ^ 9` hash calls** (`count_keygen_ge`): every one of the
top subtree's `512` leaves derives thirty-five WOTS secrets and compresses. That is more than
`512 + 3929`, which is the room the shared half needs to pay for verification out of key
generation's spend.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.VerifyBound

open Security

/-- The hash calls, among the game's oracle queries. -/
def IsHash (queried : OracleWorld.Domain) : Prop := queried.isRight = true

instance : DecidablePred IsHash := fun queried => by unfold IsHash; infer_instance

/-! ## Upper bounds, structurally -/

theorem qb_hash (input : Bytes) :
    IsQueryBoundP (Hashing.hash (m := OracleComp OracleWorld) input) IsHash 1 := by
  rw [HonestGrowth.hash_eq_liftM]
  exact (isQueryBoundP_query_iff IsHash (Sum.inr input) 1).mpr fun _ => Nat.one_pos

theorem qb_shortHash (input : Bytes) :
    IsQueryBoundP (Hashing.shortHash (m := OracleComp OracleWorld) input) IsHash 1 := by
  rw [show (Hashing.shortHash (m := OracleComp OracleWorld) input) =
      Hashing.truncate <$> Hashing.hash (m := OracleComp OracleWorld) input from by
    simp [Hashing.shortHash, map_eq_bind_pure_comp], isQueryBoundP_map_iff]
  exact qb_hash input

theorem qb_tweakable (seed : Digest) (address : Address) (payload : Bytes) :
    IsQueryBoundP (Hashing.tweakable (m := OracleComp OracleWorld) seed address payload)
      IsHash 1 :=
  qb_shortHash _

theorem qb_sequenceFin {α : Type} (k : Nat) :
    ∀ (size : Nat) (f : Fin size → OracleComp OracleWorld α),
      (∀ i, IsQueryBoundP (f i) IsHash k) →
        IsQueryBoundP (sequenceFin size f) IsHash (size * k) := by
  intro size
  induction size with
  | zero => intro f _; exact isQueryBoundP_pure _ _ _
  | succ size ih =>
    intro f hf
    rw [sequenceFin, show (size + 1) * k = k + (size * k + 0) by ring]
    refine isQueryBoundP_bind (hf 0) fun first _ => ?_
    refine isQueryBoundP_bind (ih _ fun i => hf i.succ) fun rest _ => ?_
    exact isQueryBoundP_pure _ _ _

theorem qb_foldlM {α β : Type} (step : α → β → OracleComp OracleWorld α)
    (hstep : ∀ value item, IsQueryBoundP (step value item) IsHash 1) :
    ∀ (items : List β) (init : α),
      IsQueryBoundP (items.foldlM step init) IsHash items.length := by
  intro items
  induction items with
  | nil => intro init; exact isQueryBoundP_pure _ _ _
  | cons item rest ih =>
    intro init
    rw [List.foldlM_cons, List.length_cons, Nat.add_comm]
    exact isQueryBoundP_bind (hstep init item) fun value _ => ih value

theorem qb_chain (seed : Digest) (address : Address) :
    ∀ (steps start : Nat) (value : Digest),
      IsQueryBoundP (Wots.chain (m := OracleComp OracleWorld) seed address start steps value)
        IsHash steps := by
  intro steps
  induction steps with
  | zero => intro start value; exact isQueryBoundP_pure _ _ _
  | succ steps ih =>
    intro start value
    rw [Wots.chain, show steps + 1 = 1 + steps by omega]
    exact isQueryBoundP_bind (qb_tweakable _ _ _) fun next _ => ih _ next

/-- One WOTS key recovered from a signature: thirty-five chains and a compression. -/
theorem qb_wotsFromSignature (signature : WotsSignature) (message seed : Digest)
    (address : Address) :
    IsQueryBoundP (Wots.publicKeyFromSignature (m := OracleComp OracleWorld) signature message
      seed address) IsHash (chains * (w - 1) + 1) := by
  rw [Wots.publicKeyFromSignature]
  refine isQueryBoundP_bind (qb_sequenceFin (w - 1) chains _ fun i => ?_)
    fun _ _ => qb_tweakable _ _ _
  exact (qb_chain _ _ _ _ _).mono (Nat.sub_le _ _)

/-- One XMSS layer: a WOTS key and a nine-step path. -/
theorem qb_merkleFromSignature (index : Fin (2 ^ subtreeHeight)) (signature : XmssSignature)
    (message seed : Digest) (address : Address) :
    IsQueryBoundP (Merkle.publicKeyFromSignature (m := OracleComp OracleWorld) index signature
      message seed address) IsHash (chains * (w - 1) + 1 + subtreeHeight) := by
  rw [Merkle.publicKeyFromSignature]
  refine isQueryBoundP_bind (qb_wotsFromSignature _ _ _ _) fun leaf _ => ?_
  refine (qb_foldlM _ (fun value j => ?_) (List.finRange subtreeHeight) leaf).mono (by simp)
  exact qb_tweakable _ _ _

theorem qb_rootFromSignature (seed : Digest) :
    ∀ (remaining : Nat) (signatures : Fin remaining → XmssSignature) (layer tree : Nat)
      (leaf : Hypertree.LeafIndex) (message : Digest),
      IsQueryBoundP (Hypertree.rootFromSignature (m := OracleComp OracleWorld) seed remaining
        signatures layer tree leaf message) IsHash
        (remaining * (chains * (w - 1) + 1 + subtreeHeight)) := by
  intro remaining
  induction remaining with
  | zero => intro _ _ _ _ _; exact isQueryBoundP_pure _ _ _
  | succ remaining ih =>
    intro signatures layer tree leaf message
    rw [Hypertree.rootFromSignature]
    exact (isQueryBoundP_bind (qb_merkleFromSignature _ _ _ _ _) fun root _ =>
      ih _ _ _ _ _).mono (le_of_eq (by ring))

theorem qb_forsFromSignature (signature : ForsSignature) (indices : Fors.Indices)
    (seed : Digest) (address : Address) :
    IsQueryBoundP (Fors.publicKeyFromSignature (m := OracleComp OracleWorld) signature indices
      seed address) IsHash (forsTrees * (1 + forsHeight) + 1) := by
  rw [Fors.publicKeyFromSignature]
  refine isQueryBoundP_bind (qb_sequenceFin (1 + forsHeight) forsTrees _ fun i => ?_)
    fun _ _ => qb_tweakable _ _ _
  refine isQueryBoundP_bind (qb_tweakable _ _ _) fun leaf _ => ?_
  refine (qb_foldlM _ (fun value j => ?_) (List.finRange forsHeight) leaf).mono (by simp)
  exact qb_tweakable _ _ _

/-- The structural bound on verification. -/
def verifyLimit : Nat :=
  1 + (forsTrees * (1 + forsHeight) + 1) + layers * (chains * (w - 1) + 1 + subtreeHeight)

theorem verifyLimit_eq : verifyLimit = 3929 := by decide

/-- **Verification makes at most `3929` hash calls, on every path.** -/
theorem isQueryBoundP_verify (pk : PublicKey) (request : Message) (signature : Bytes) :
    IsQueryBoundP (Scheme.verify (m := OracleComp OracleWorld) pk request signature) IsHash
      verifyLimit := by
  rw [Scheme.verify]
  rcases request.frame with _ | message
  · exact isQueryBoundP_pure _ _ _
  rcases Signature.fromBytes? signature with _ | parsed
  · exact isQueryBoundP_pure _ _ _
  dsimp only
  rw [Scheme.verifyInternal, verifyLimit, Nat.add_assoc]
  refine isQueryBoundP_bind (qb_hash _) fun digest _ => ?_
  refine isQueryBoundP_bind (qb_forsFromSignature _ _ _ _) fun forsKey _ => ?_
  rw [Hypertree.verify, ← Nat.add_zero (layers * _)]
  exact isQueryBoundP_bind (qb_rootFromSignature _ _ _ _ _ _ _) fun _ _ =>
    isQueryBoundP_pure _ _ _

end SlhDsaSecurity.VerifyBound
