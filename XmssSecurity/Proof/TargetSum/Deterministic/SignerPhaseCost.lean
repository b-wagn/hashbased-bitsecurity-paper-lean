import XmssSecurity.Proof.TargetSum.Deterministic.SignerCost
import XmssSecurity.Proof.TargetSum.Deterministic.CostState
import XmssSecurity.Proof.TargetSum.Deterministic.RequestSampling

/-! Transfer the full adaptive adversary phase to table signing, retaining the original
cost of two hashes per signing attempt and one hash per direct query. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Seeded

noncomputable def chargedSigning (weight : Nat)
    (computation : OracleComp OracleWorld (Option Signature)) :
    StateT CostState ProbComp (Option Signature) := fun state =>
  (fun result => (result.1.1, result.2, state.2 + weight * result.1.2)) <$>
    (simulateQ romImpl (countHashQueries computation)).run state.1

theorem chargedSigning_cache_le (weight : Nat)
    (computation : OracleComp OracleWorld (Option Signature)) (state : CostState)
    (result : Option Signature × CostState)
    (hresult : result ∈ support ((chargedSigning weight computation).run state)) :
    state.1 ≤ result.2.1 := by
  change result ∈ support ((fun result =>
    (result.1.1, result.2, state.2 + weight * result.1.2)) <$>
      (simulateQ romImpl (countHashQueries computation)).run state.1) at hresult
  rw [support_map] at hresult
  obtain ⟨record, hrecord, rfl⟩ := hresult
  exact xmssRom_cache_le _ _ _ hrecord

theorem chargedSigning_one
    (computation : OracleComp OracleWorld (Option Signature)) (state : CostState) :
    (chargedSigning 1 computation).run state =
      (simulateQ (worldHandler costHash) computation).run state := by
  rw [run_costWorld]
  simp only [chargedSigning, StateT.run, one_mul]

noncomputable def tablePhaseCostImpl (randomizers : RandomizerOutputs)
    (secretKey : XmssSecurity.TargetSum.SecretKey) :
    QueryImpl (OracleWorld + SigningSpec) (StateT CostState ProbComp) :=
  worldHandler costHash + fun (request : SignRequest) =>
    chargedSigning 2 ((tableScheme randomizers).sign secretKey request.epoch request.message)

theorem tablePhaseCostImpl_cache_le (randomizers : RandomizerOutputs)
    (secretKey : XmssSecurity.TargetSum.SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (state : CostState) (result : (OracleWorld + SigningSpec).Range input × CostState)
    (hresult : result ∈ support ((tablePhaseCostImpl randomizers secretKey input).run state)) :
    state.1 ≤ result.2.1 := by
  cases input with
  | inl input =>
      change result ∈ support (((worldHandler costHash) input).run state) at hresult
      rw [run_costQuery, support_map] at hresult
      obtain ⟨record, hrecord, rfl⟩ := hresult
      exact romImpl_query_cache_le input state.1 record hrecord
  | inr request => exact chargedSigning_cache_le 2 _ state result hresult

theorem evalDist_cost_sign_eq_table
    (seed : MasterSeed) (secretKey : XmssSecurity.TargetSum.SecretKey)
    (randomizers : RandomizerOutputs) (leafIndex : LeafIndex) (message : Message)
    (state : CostState)
    (hcache : ∀ position, state.1 (randomizerInputs secretKey.parameter seed position) =
      some (randomizers position)) :
    𝒟[(simulateQ (worldHandler costHash)
      (scheme.sign ⟨seed, secretKey⟩ leafIndex message)).run state] =
      𝒟[(chargedSigning 2
        ((tableScheme randomizers).sign secretKey leafIndex message)).run state] := by
  rw [run_costWorld, evalDist_map,
    evalDist_counted_sign_eq_twice_tableSign _ _ _ _ _ _ hcache, evalDist_map]
  simp only [chargedSigning, StateT.run, evalDist_map, Functor.map_map]

theorem evalDist_cost_runSigning_eq_table
    {α : Type} (seed : MasterSeed) (secretKey : XmssSecurity.TargetSum.SecretKey)
    (randomizers : RandomizerOutputs)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CostState)
    (hcache : ∀ position, state.1 (randomizerInputs secretKey.parameter seed position) =
      some (randomizers position)) :
    𝒟[(simulateQ (worldHandler costHash)
      (runSigning (fun (request : SignRequest) => sign ⟨seed, secretKey⟩ request.epoch request.message)
        computation)).run state] =
      𝒟[(simulateQ (tablePhaseCostImpl randomizers secretKey) computation).run state] := by
  rw [simulateQ_runSigning]
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      have hquery : 𝒟[(((worldHandler costHash) + fun (request : SignRequest) =>
          simulateQ (worldHandler costHash)
            (liftM (sign ⟨seed, secretKey⟩ request.epoch request.message :
              OracleComp HashSpec (Option Signature)) : OracleComp OracleWorld _)) input).run state] =
          𝒟[(tablePhaseCostImpl randomizers secretKey input).run state] := by
        cases input with
        | inl input => rfl
        | inr request => exact evalDist_cost_sign_eq_table _ _ _ _ _ _ hcache
      rw [evalDist_bind, hquery, ← evalDist_bind]
      apply evalDist_bind_congr
      intro result hresult
      exact ih result.1 result.2 (fun position =>
        tablePhaseCostImpl_cache_le randomizers secretKey input state result hresult (hcache position))

theorem tablePhaseCost_le_of_hashQueryBound
    {α : Type} (seed : MasterSeed) (secretKey : XmssSecurity.TargetSum.SecretKey)
    (randomizers : RandomizerOutputs)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec)
    (hcache : ∀ position, cache (randomizerInputs secretKey.parameter seed position) =
      some (randomizers position)) (q : Nat)
    (hbound : HashQueryBound
      (runSigning (fun (request : SignRequest) => sign ⟨seed, secretKey⟩ request.epoch request.message)
        computation) cache q)
    (result : α × CostState)
    (hresult : result ∈ support
      ((simulateQ (tablePhaseCostImpl randomizers secretKey) computation).run (cache, 0))) :
    result.2.2 ≤ q := by
  apply (hashQueryBound_iff_costState _ cache q).1 hbound result
  rw [mem_support_iff_of_evalDist_eq
    (evalDist_cost_runSigning_eq_table _ _ _ computation (cache, 0) hcache)]
  exact hresult

/-- info: 'XmssSecurity.TargetSum.Seeded.evalDist_cost_runSigning_eq_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalDist_cost_runSigning_eq_table

/-- info: 'XmssSecurity.TargetSum.Seeded.tablePhaseCost_le_of_hashQueryBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tablePhaseCost_le_of_hashQueryBound

end XmssSecurity.TargetSum.Seeded
