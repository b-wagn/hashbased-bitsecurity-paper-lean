import XmssSecurity.Proof.TargetSum.Deterministic.SignerCost
import XmssSecurity.Proof.Generic.Deterministic.CostState
import XmssSecurity.Proof.Generic.Deterministic.RequestSampling
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability
/-! Transfer the full adaptive adversary phase to table signing, retaining the original
cost of two hashes per signing attempt and one hash per direct query. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Seeded

noncomputable def chargedSigning (weight : Nat)
    (computation : OracleComp OracleWorld (Option Generic.Signature)) :
    StateT Generic.Seeded.CostState ProbComp (Option Generic.Signature) := fun state =>
  (fun result => (result.1.1, result.2, state.2 + weight * result.1.2)) <$>
    (simulateQ Generic.romImpl (Generic.countHashQueries computation)).run state.1

theorem chargedSigning_cache_le (weight : Nat)
    (computation : OracleComp OracleWorld (Option Generic.Signature)) (state : Generic.Seeded.CostState)
    (result : Option Generic.Signature × Generic.Seeded.CostState)
    (hresult : result ∈ support ((chargedSigning weight computation).run state)) :
    state.1 ≤ result.2.1 := by
  change result ∈ support ((fun result =>
    (result.1.1, result.2, state.2 + weight * result.1.2)) <$>
      (simulateQ Generic.romImpl (Generic.countHashQueries computation)).run state.1) at hresult
  rw [support_map] at hresult
  obtain ⟨record, hrecord, rfl⟩ := hresult
  exact Generic.xmssRom_cache_le _ _ _ hrecord

noncomputable def tablePhaseCostImpl (randomizers : Generic.Seeded.RandomizerOutputs)
    (secretKey : Generic.SecretKey) :
    QueryImpl (OracleWorld + Generic.SigningSpec) (StateT Generic.Seeded.CostState ProbComp) :=
  Generic.Seeded.worldHandler Generic.Seeded.costHash + fun (request : Generic.SignRequest) =>
    chargedSigning 2 ((Generic.Seeded.tableScheme randomizers).sign secretKey request.epoch request.message)

theorem tablePhaseCostImpl_cache_le (randomizers : Generic.Seeded.RandomizerOutputs)
    (secretKey : Generic.SecretKey) (input : (OracleWorld + Generic.SigningSpec).Domain)
    (state : Generic.Seeded.CostState) (result : (OracleWorld + Generic.SigningSpec).Range input × Generic.Seeded.CostState)
    (hresult : result ∈ support ((tablePhaseCostImpl randomizers secretKey input).run state)) :
    state.1 ≤ result.2.1 := by
  cases input with
  | inl input =>
      change result ∈ support (((Generic.Seeded.worldHandler Generic.Seeded.costHash) input).run state) at hresult
      rw [Generic.Seeded.run_costQuery, support_map] at hresult
      obtain ⟨record, hrecord, rfl⟩ := hresult
      exact Generic.romImpl_query_cache_le input state.1 record hrecord
  | inr request => exact chargedSigning_cache_le 2 _ state result hresult

theorem evalDist_cost_sign_eq_table
    (seed : MasterSeed) (secretKey : Generic.SecretKey)
    (randomizers : Generic.Seeded.RandomizerOutputs) (leafIndex : LeafIndex) (message : Message)
    (state : Generic.Seeded.CostState)
    (hcache : ∀ position, state.1 (Generic.Seeded.randomizerInputs secretKey.parameter seed position) =
      some (randomizers position)) :
    𝒟[(simulateQ (Generic.Seeded.worldHandler Generic.Seeded.costHash)
      (Generic.Seeded.scheme.sign ⟨seed, secretKey⟩ leafIndex message)).run state] =
      𝒟[(chargedSigning 2
        ((Generic.Seeded.tableScheme randomizers).sign secretKey leafIndex message)).run state] := by
  rw [Generic.Seeded.run_costWorld, evalDist_map,
    evalDist_counted_sign_eq_twice_tableSign _ _ _ _ _ _ hcache, evalDist_map]
  simp only [chargedSigning, StateT.run, evalDist_map, Functor.map_map]

theorem evalDist_cost_runSigning_eq_table
    {α : Type} (seed : MasterSeed) (secretKey : Generic.SecretKey)
    (randomizers : Generic.Seeded.RandomizerOutputs)
    (computation : OracleComp (OracleWorld + Generic.SigningSpec) α) (state : Generic.Seeded.CostState)
    (hcache : ∀ position, state.1 (Generic.Seeded.randomizerInputs secretKey.parameter seed position) =
      some (randomizers position)) :
    𝒟[(simulateQ (Generic.Seeded.worldHandler Generic.Seeded.costHash)
      (Generic.Seeded.runSigning (fun (request : Generic.SignRequest) => Generic.Seeded.sign ⟨seed, secretKey⟩ request.epoch request.message)
        computation)).run state] =
      𝒟[(simulateQ (tablePhaseCostImpl randomizers secretKey) computation).run state] := by
  rw [Generic.Seeded.simulateQ_runSigning]
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      have hquery : 𝒟[(((Generic.Seeded.worldHandler Generic.Seeded.costHash) + fun (request : Generic.SignRequest) =>
          simulateQ (Generic.Seeded.worldHandler Generic.Seeded.costHash)
            (liftM (Generic.Seeded.sign ⟨seed, secretKey⟩ request.epoch request.message :
              OracleComp HashSpec (Option Generic.Signature)) : OracleComp OracleWorld _)) input).run state] =
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
    {α : Type} (seed : MasterSeed) (secretKey : Generic.SecretKey)
    (randomizers : Generic.Seeded.RandomizerOutputs)
    (computation : OracleComp (OracleWorld + Generic.SigningSpec) α) (cache : QueryCache HashSpec)
    (hcache : ∀ position, cache (Generic.Seeded.randomizerInputs secretKey.parameter seed position) =
      some (randomizers position)) (q : Nat)
    (hbound : Generic.HashQueryBound
      (Generic.Seeded.runSigning (fun (request : Generic.SignRequest) => Generic.Seeded.sign ⟨seed, secretKey⟩ request.epoch request.message)
        computation) cache q)
    (result : α × Generic.Seeded.CostState)
    (hresult : result ∈ support
      ((simulateQ (tablePhaseCostImpl randomizers secretKey) computation).run (cache, 0))) :
    result.2.2 ≤ q := by
  apply (Generic.Seeded.hashQueryBound_iff_costState _ cache q).1 hbound result
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
