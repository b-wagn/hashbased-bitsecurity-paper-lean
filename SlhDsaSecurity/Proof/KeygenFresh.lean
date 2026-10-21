import SlhDsaSecurity.Statement.Scheme
import SlhDsaSecurity.Proof.HashSeparation
import VCVio.OracleComp.QueryTracking.QueryBound

/-! The final top-tree address is absent throughout the preceding key-generation work. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.KeygenUniform

def rootAddress : Address :=
  Merkle.nodeAddress (Hypertree.address (layers - 1) 0) subtreeHeight 0

def RootQuery (seed : Digest) (payload : Bytes) : OracleWorld.Domain → Prop :=
  fun input => input = .inr (Hashing.tweakableInput seed rootAddress payload)

instance (seed : Digest) (payload : Bytes) : DecidablePred (RootQuery seed payload) :=
  fun _ => inferInstanceAs (Decidable (_ = _))

theorem tweakable_avoids_root (seed : Digest) (address : Address) (payload target : Bytes)
    (hne : address ≠ rootAddress) :
    (Hashing.tweakable seed address payload : OracleComp OracleWorld Digest).IsQueryBoundP
      (RootQuery seed target) 0 := by
  have hinput : Hashing.tweakableInput seed address payload ≠
      Hashing.tweakableInput seed rootAddress target := fun h =>
    hne (Hashing.tweakableInput_injective h).2.1
  simp only [Hashing.tweakable, Hashing.shortHash, Hashing.hash, bind_pure_comp,
    OracleComp.isQueryBoundP_map_iff]
  change (liftM (OracleWorld.query (.inr (Hashing.tweakableInput seed address payload))) :
    OracleComp OracleWorld HashOutput).IsQueryBoundP (RootQuery seed target) 0
  simp [RootQuery, hinput]

theorem chain_avoids_root (seed : Digest) (address : Address)
    (hkind : address.kind = .wotsHash) (start steps : Nat) (value : Digest) (target : Bytes) :
    (Wots.chain seed address start steps value : OracleComp OracleWorld Digest).IsQueryBoundP
      (RootQuery seed target) 0 := by
  induction steps generalizing start value with
  | zero => simp [Wots.chain]
  | succ steps ih =>
      rw [Wots.chain]
      refine OracleComp.isQueryBoundP_bind (m := 0)
        (tweakable_avoids_root seed _ _ target ?_) (fun value _ => ih _ _)
      intro heq
      have := congrArg Address.kind heq
      simp [rootAddress, Merkle.nodeAddress, Address.setTypeAndClear, hkind] at this

theorem sequenceFin_avoids_root {α : Type} {size : Nat}
    (computation : Fin size → OracleComp OracleWorld α) (seed : Digest) (target : Bytes)
    (hzero : ∀ index, (computation index).IsQueryBoundP (RootQuery seed target) 0) :
    (sequenceFin size computation).IsQueryBoundP (RootQuery seed target) 0 := by
  induction size with
  | zero => simp [sequenceFin]
  | succ size ih =>
      rw [sequenceFin]
      refine OracleComp.isQueryBoundP_bind (m := 0) (hzero 0) ?_
      intro head _
      refine OracleComp.isQueryBoundP_bind (m := 0)
        (ih (fun index => computation index.succ) (fun index => hzero index.succ)) ?_
      intro tail _
      simp

theorem wots_avoids_root (secretSeed seed : Digest) (address : Address)
    (hkind : address.kind = .wotsHash) (target : Bytes) :
    (Wots.publicKey secretSeed seed address : OracleComp OracleWorld Digest).IsQueryBoundP
      (RootQuery seed target) 0 := by
  unfold Wots.publicKey
  refine OracleComp.isQueryBoundP_bind (m := 0) ?_ ?_
  · apply sequenceFin_avoids_root
    intro index
    refine OracleComp.isQueryBoundP_bind (m := 0) ?_ ?_
    · unfold Hashing.derive
      apply tweakable_avoids_root
      intro heq
      have := congrArg Address.kind heq
      simp [Wots.secretAddress, rootAddress, Merkle.nodeAddress, Address.setTypeAndClear] at this
    · intro secret _
      apply chain_avoids_root
      exact hkind
  · intro endpoints _
    apply tweakable_avoids_root
    intro heq
    have := congrArg Address.kind heq
    simp [Wots.publicKeyAddress, rootAddress, Merkle.nodeAddress, Address.setTypeAndClear] at this

theorem node_avoids_root (secretSeed seed : Digest) (address : Address)
    (height index : Nat) (hheight : height < subtreeHeight) (target : Bytes) :
    (Merkle.node secretSeed seed address height index : OracleComp OracleWorld Digest).IsQueryBoundP
      (RootQuery seed target) 0 := by
  induction height generalizing index with
  | zero =>
      exact wots_avoids_root secretSeed seed _ rfl target
  | succ height ih =>
      rw [Merkle.node]
      refine OracleComp.isQueryBoundP_bind (m := 0) (ih _ (by omega)) ?_
      intro left _
      refine OracleComp.isQueryBoundP_bind (m := 0) (ih _ (by omega)) ?_
      intro right _
      apply tweakable_avoids_root
      intro heq
      have hh := congrArg (fun a => a.chainOrHeight.toNat) heq
      have hsmall : height + 1 < 2 ^ 32 := by change height + 1 < 9 at hheight; omega
      simp [rootAddress, Merkle.nodeAddress, Address.setTypeAndClear,
        subtreeHeight, BitVec.toNat_ofNat] at hh
      change height + 1 < 9 at hheight
      omega

noncomputable abbrev rom : QueryImpl OracleWorld (StateT (QueryCache HashSpec) ProbComp) :=
  XmssSecurity.RandomOracleModel.impl Bytes HashOutput

/-- No call to a missing input leaves that cache entry missing. Uniform coins are harmless. -/
theorem cache_none_of_zero_query_bound {α : Type}
    (computation : OracleComp OracleWorld α) (target : Bytes)
    (initialCache finalCache : QueryCache HashSpec) (result : α)
    (hbound : computation.IsQueryBoundP (· = .inr target) 0)
    (hnone : initialCache target = none)
    (hmem : (result, finalCache) ∈ support ((simulateQ rom computation).run initialCache)) :
    finalCache target = none := by
  induction computation using OracleComp.inductionOn generalizing
      initialCache finalCache result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      exact hmem.2 ▸ hnone
  | query_bind queried next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      have hne : queried ≠ .inr target := by simpa using hbound.1
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨output, middleCache⟩, hquery, hrest⟩ := hmem
      have hmiddle : middleCache target = none := by
        rcases queried with uniform | queried
        · have hcache : middleCache = initialCache := by
            symm
            simpa [rom, XmssSecurity.RandomOracleModel.impl, unifFwdImpl] using hquery
          exact hcache ▸ hnone
        · change (output, middleCache) ∈ support ((randomOracle queried).run initialCache) at hquery
          have hne' : target ≠ queried := fun heq => hne (heq ▸ rfl)
          cases hqueried : initialCache queried with
          | none =>
              rw [QueryImpl.withCaching_run_none _ hqueried, support_map] at hquery
              obtain ⟨sampled, _hsampled, heq⟩ := hquery
              cases heq
              simpa only [QueryCache.cacheQuery_of_ne initialCache output hne'] using hnone
          | some cached =>
              rw [QueryImpl.withCaching_run_some _ hqueried, support_pure,
                Set.mem_singleton_iff] at hquery
              cases hquery
              exact hnone
      exact ih output middleCache finalCache result
        (by simpa [hne] using hbound.2 output) hmiddle hrest

def topChildren (secretSeed seed : Digest) : OracleComp OracleWorld (Digest × Digest) := do
  let left ← Merkle.node secretSeed seed (Hypertree.address (layers - 1) 0) 8 0
  let right ← Merkle.node secretSeed seed (Hypertree.address (layers - 1) 0) 8 1
  return (left, right)

theorem topChildren_avoids_root (secretSeed seed : Digest) (target : Bytes) :
    (topChildren secretSeed seed).IsQueryBoundP (RootQuery seed target) 0 := by
  unfold topChildren
  refine OracleComp.isQueryBoundP_bind (m := 0)
    (node_avoids_root secretSeed seed _ 8 0 (by decide) target) ?_
  intro left _
  refine OracleComp.isQueryBoundP_bind (m := 0)
    (node_avoids_root secretSeed seed _ 8 1 (by decide) target) ?_
  intro right _
  simp

theorem topChildren_root_fresh (secretSeed seed : Digest)
    (result : (Digest × Digest) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ rom (topChildren secretSeed seed)).run ∅))
    (payload : Bytes) : result.2 (Hashing.tweakableInput seed rootAddress payload) = none :=
  cache_none_of_zero_query_bound (topChildren secretSeed seed) _ ∅ result.2 result.1
    (topChildren_avoids_root secretSeed seed payload) (by simp) hresult

end SlhDsaSecurity.KeygenUniform
