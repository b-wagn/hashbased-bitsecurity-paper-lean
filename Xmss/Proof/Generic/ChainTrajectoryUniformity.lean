import Xmss.Proof.Generic.ConcreteQueryBound

open OracleComp OracleSpec ENNReal

namespace Xmss.Generic

variable [Code]

noncomputable local instance chainTrajectorySampleableDigest : SampleableType Digest :=
  SampleableType.ofFintype Digest

omit [Code] in
@[simp]
theorem Vector.back_push {n : Nat} (values : Vector α n) (value : α) :
    (values.push value).back = value := by
  symm
  exact Vector.back_eq_of_push_eq (Vector.push_pop_back (values.push value)).symm

def Wots.chainTrajectory
    (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (position : Nat) : (steps : Nat) → Digest →
      OracleComp HashSpec (Vector Digest (steps + 1))
  | 0, value => pure (Vector.ofFn fun _ => value)
  | steps + 1, value => do
      let values ← chainTrajectory parameter leafIndex chain position steps value
      if hvalid : position + steps < chainLength - 1 then
        let next ← Hashing.chainHash parameter leafIndex chain
          ⟨position + steps, hvalid⟩ values.back
        return values.push next
      else
        return values.push 0

@[simp]
theorem Wots.chainTrajectory_zero
    (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (position : Nat) (value : Digest) :
    Wots.chainTrajectory parameter leafIndex chain position 0 value =
      pure (Vector.ofFn fun _ => value) := rfl

theorem Wots.chainTrajectory_succ
    (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (position steps : Nat) (value : Digest) :
    Wots.chainTrajectory parameter leafIndex chain position (steps + 1) value = (do
      let values ← Wots.chainTrajectory parameter leafIndex chain position steps value
      if hvalid : position + steps < chainLength - 1 then
        let next ← Hashing.chainHash parameter leafIndex chain
          ⟨position + steps, hvalid⟩ values.back
        return values.push next
      else
        return values.push 0) := rfl

@[simp]
theorem Wots.chainTrajectory_back
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (leafIndex : LeafIndex) (chain : ChainIndex) (position steps : Nat)
    (value : Digest) :
    (evalWithAnswerFn (CacheReplay.answerFn cache)
      (Wots.chainTrajectory parameter leafIndex chain position steps value)).back =
      Wots.walk (CacheView.chainStep cache parameter leafIndex chain)
        position steps value := by
  induction steps with
  | zero =>
      change value = value
      rfl
  | succ steps ih =>
      rw [Wots.chainTrajectory_succ]
      simp only [evalWithAnswerFn_bind, ih, Wots.walk]
      split <;> simp_all [Hashing.chainHash, CacheView.chainStep,
        CacheView.chainInput, CacheView.tweakableHash]

theorem Wots.chainTrajectory_getElem
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (leafIndex : LeafIndex) (chain : ChainIndex) (position steps offset : Nat)
    (value : Digest) (hoffset : offset < steps + 1) :
    (evalWithAnswerFn (CacheReplay.answerFn cache)
      (Wots.chainTrajectory parameter leafIndex chain position steps value))[offset] =
      Wots.walk (CacheView.chainStep cache parameter leafIndex chain)
        position offset value := by
  induction steps generalizing offset with
  | zero =>
      have : offset = 0 := by omega
      subst offset
      rfl
  | succ steps ih =>
      rw [Wots.chainTrajectory_succ]
      simp only [evalWithAnswerFn_bind]
      split <;> rename_i hvalid
      · simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
        by_cases hlower : offset < steps + 1
        · rw [Vector.getElem_push_lt]
          exact ih offset hlower
        · have hlast : offset = steps + 1 := by omega
          subst offset
          rw [Vector.getElem_push_eq, Wots.chainTrajectory_back]
          simp [Wots.walk, hvalid, Hashing.chainHash,
            CacheView.chainStep, CacheView.chainInput,
            CacheView.tweakableHash]
      · simp only [evalWithAnswerFn_pure]
        by_cases hlower : offset < steps + 1
        · rw [Vector.getElem_push_lt]
          exact ih offset hlower
        · have hlast : offset = steps + 1 := by omega
          subst offset
          rw [Vector.getElem_push_eq]
          simp [Wots.walk, CacheView.chainStep, hvalid]

theorem Wots.chainTrajectory_queryBound_zero_of_avoids
    (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (position steps : Nat) (value : Digest) (targetDomain : HashDomain)
    (havoid : ∀ offset, offset < steps →
      ∀ hvalid : position + offset < chainLength - 1,
        HashDomain.chain leafIndex chain ⟨position + offset, hvalid⟩ ≠ targetDomain) :
    (Wots.chainTrajectory parameter leafIndex chain position steps value).IsQueryBoundP
      (AtHashAddress parameter targetDomain) 0 := by
  induction steps with
  | zero => simp [Wots.chainTrajectory]
  | succ steps ih =>
      rw [Wots.chainTrajectory_succ]
      refine OracleComp.isQueryBoundP_bind (m := 0)
        (ih fun offset hoffset => havoid offset (by omega)) ?_
      intro values _
      split
      · exact OracleComp.isQueryBoundP_bind (m := 0)
          (Hashing.tweakableHash_queryBound_atOtherAddress parameter targetDomain
            (.chain leafIndex chain ⟨position + steps, by assumption⟩)
            (Hashing.digestBytes values.back) (havoid steps (by omega) _))
          (fun next _ => OracleComp.isQueryBoundP_pure
            (p := AtHashAddress parameter targetDomain) (values.push next) 0)
      · exact OracleComp.isQueryBoundP_pure
          (p := AtHashAddress parameter targetDomain) (values.push 0) 0


end Xmss.Generic
