import XmssSecurity.Proof.TargetSum.Deterministic.SignerReferenceCost
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Represent the table signer's charge by repeated consistent hash queries. This lets
the existing seed-avoidance and memoization budget arguments retain both hashes per attempt. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.Seeded

open DeterministicSigning

attribute [local irreducible] Seeded.tableSign

noncomputable def twiceHashQuery : QueryImpl HashSpec (OracleComp HashSpec) := fun input => do
  let answer ← liftM (HashSpec.query input)
  let _ ← liftM (HashSpec.query input)
  pure answer

noncomputable def twiceHashQueries {α : Type} (computation : OracleComp HashSpec α) :
    OracleComp HashSpec α := simulateQ twiceHashQuery computation

theorem evalDist_cost_twiceHashQuery (input : HashInput) (state : Seeded.CostState) :
    𝒟[(simulateQ Seeded.costHash (twiceHashQuery input)).run state] =
      𝒟[(weightedCostHash 2 input).run state] := by
  simp only [twiceHashQuery, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
    StateT.run_bind, StateT.run_pure]
  unfold Seeded.costHash weightedCostHash
  simp only [StateT.run, bind_assoc, pure_bind]
  apply evalDist_bind_congr
  intro result hresult
  change 𝒟[(do
    let next ← (randomOracle (spec := HashSpec) input).run result.2
    pure (result.1, next.2, state.2 + 1 + 1))] =
      𝒟[pure (result.1, result.2, state.2 + 2)]
  rw [QueryImpl.withCaching_run_some _ (DeterministicSigning.query_caches input state.1 result hresult), pure_bind]

theorem evalDist_cost_twiceHashQueries {α : Type}
    (computation : OracleComp HashSpec α) (state : Seeded.CostState) :
    𝒟[(simulateQ Seeded.costHash (twiceHashQueries computation)).run state] =
      𝒟[(simulateQ (weightedCostHash 2) computation).run state] := by
  rw [twiceHashQueries, ← QueryImpl.simulateQ_compose]
  apply evalDist_simulateQ_run_congr
  intro input state
  exact evalDist_cost_twiceHashQuery input state

theorem evalDist_cost_twiceHashQueries_lift {α : Type}
    (computation : OracleComp HashSpec α) (state : Seeded.CostState) :
    𝒟[(simulateQ (Seeded.worldHandler Seeded.costHash)
      (liftM (twiceHashQueries computation) : OracleComp OracleWorld α)).run state] =
      𝒟[(simulateQ (Seeded.worldHandler (weightedCostHash 2))
        (liftM computation : OracleComp OracleWorld α)).run state] := by
  simp only [Seeded.worldHandler, QueryImpl.simulateQ_add_liftM_right]
  exact evalDist_cost_twiceHashQueries computation state

noncomputable def chargedTableRun {α : Type} (randomizers : Seeded.RandomizerOutputs)
    (secretKey : Generic.SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) : OracleComp OracleWorld α :=
  Seeded.runSigning (fun (request : SignRequest) => twiceHashQueries
    (Seeded.tableSign randomizers secretKey request.epoch request.message)) computation

theorem evalDist_cost_chargedTableRun {α : Type} (randomizers : Seeded.RandomizerOutputs)
    (secretKey : Generic.SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : Seeded.CostState) :
    𝒟[(simulateQ (Seeded.worldHandler Seeded.costHash)
      (chargedTableRun randomizers secretKey computation)).run state] =
      𝒟[(simulateQ (tablePhaseCostImpl randomizers secretKey) computation).run state] := by
  rw [chargedTableRun, Seeded.simulateQ_runSigning]
  apply evalDist_simulateQ_run_congr
  intro input state
  cases input with
  | inl input => rfl
  | inr request =>
      simp only [tablePhaseCostImpl, chargedSigning_eq_weightedCostWorld]
      exact evalDist_cost_twiceHashQueries_lift
        (Seeded.tableSign randomizers secretKey request.epoch request.message) state

def TablePhaseCostBound {α : Type} (randomizers : Seeded.RandomizerOutputs)
    (secretKey : Generic.SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) (q : Nat) : Prop :=
  ∀ result ∈ support
    ((simulateQ (tablePhaseCostImpl randomizers secretKey) computation).run (cache, 0)),
      result.2.2 ≤ q

theorem tablePhaseCostBound_iff_hashQueryBound {α : Type}
    (randomizers : Seeded.RandomizerOutputs) (secretKey : Generic.SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) (q : Nat) :
    TablePhaseCostBound randomizers secretKey computation cache q ↔
      HashQueryBound (chargedTableRun randomizers secretKey computation) cache q := by
  rw [Seeded.hashQueryBound_iff_costState]
  simp only [TablePhaseCostBound, mem_support_iff_of_evalDist_eq
    (evalDist_cost_chargedTableRun randomizers secretKey computation (cache, 0))]

/-- Remove seed-dependent cache programming while retaining the complete signer charge. -/
theorem tablePhaseCostBound_of_seed_caches {α : Type}
    (randomizers : Seeded.RandomizerOutputs) (secretKey : Generic.SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (q : Nat) (inputs : List HashInput) (caches : MasterSeed → QueryCache HashSpec)
    (cache : QueryCache HashSpec) (hsize : inputs.length + q < 2 ^ 256)
    (hagree : ∀ seed, ¬SeedHitLog inputs seed →
      Seeded.AgreeOutside (fun input => SeedHit input seed) (caches seed) cache)
    (hbound : ∀ seed, ¬SeedHitLog inputs seed →
      TablePhaseCostBound randomizers secretKey computation (caches seed) q) :
    TablePhaseCostBound randomizers secretKey computation cache q := by
  rw [tablePhaseCostBound_iff_hashQueryBound]
  apply Seeded.hashQueryBound_of_seed_caches _ q inputs caches cache hsize hagree
  intro seed hseed
  exact (tablePhaseCostBound_iff_hashQueryBound _ _ _ _ _).1 (hbound seed hseed)

/-- Repeated deterministic signing requests can be memoized without increasing cost. -/
theorem tablePhaseCostBound_memoize {α : Type}
    (randomizers : Seeded.RandomizerOutputs) (secretKey : Generic.SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) (q : Nat)
    (hbound : TablePhaseCostBound randomizers secretKey computation cache q) :
    TablePhaseCostBound randomizers secretKey (DeterministicSigning.memoize computation ∅) cache q := by
  rw [tablePhaseCostBound_iff_hashQueryBound] at hbound ⊢
  unfold chargedTableRun at hbound ⊢
  exact Seeded.hashQueryBound_runSigning_memoize
    (fun (request : SignRequest) => twiceHashQueries
      (Seeded.tableSign randomizers secretKey request.epoch request.message)) computation cache q hbound

theorem tablePhaseCostBound_map_iff {α β : Type}
    (randomizers : Seeded.RandomizerOutputs) (secretKey : Generic.SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (f : α → β)
    (cache : QueryCache HashSpec) (q : Nat) :
    TablePhaseCostBound randomizers secretKey (f <$> computation) cache q ↔
      TablePhaseCostBound randomizers secretKey computation cache q := by
  simp only [TablePhaseCostBound, simulateQ_map, StateT.run_map, support_map,
    Set.forall_mem_image]

theorem tablePhaseCostBound_withRequestLog_iff {α : Type}
    (randomizers : Seeded.RandomizerOutputs) (secretKey : Generic.SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) (q : Nat) :
    TablePhaseCostBound randomizers secretKey (DeterministicSigning.withRequestLog computation) cache q ↔
      TablePhaseCostBound randomizers secretKey computation cache q := by
  have h := tablePhaseCostBound_map_iff randomizers secretKey
    (DeterministicSigning.withRequestLog computation) Prod.fst cache q
  rw [DeterministicSigning.fst_withRequestLog] at h
  exact h.symm

theorem tablePhaseCostBound_logged_memoize {α : Type}
    (randomizers : Seeded.RandomizerOutputs) (secretKey : Generic.SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) (q : Nat)
    (hbound : TablePhaseCostBound randomizers secretKey (DeterministicSigning.withRequestLog computation) cache q) :
    TablePhaseCostBound randomizers secretKey (DeterministicSigning.withRequestLog (DeterministicSigning.memoize computation ∅)) cache q := by
  rw [tablePhaseCostBound_withRequestLog_iff] at hbound ⊢
  exact tablePhaseCostBound_memoize randomizers secretKey computation cache q hbound

theorem referencePhaseCost_logged_memo_le_of_table {α : Type}
    (secretKey : Generic.SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) (q : Nat)
    (hbound : ∀ randomizers,
      TablePhaseCostBound randomizers secretKey (DeterministicSigning.withRequestLog computation) cache q)
    (result : (α × QueryLog SigningSpec) × Seeded.CostState)
    (hresult : result ∈ support ((simulateQ (referencePhaseCostImpl secretKey)
      (DeterministicSigning.withRequestLog (DeterministicSigning.memoize computation ∅))).run (cache, 0))) :
    result.2.2 ≤ q := by
  have hfresh : DeterministicSigning.FreshRequests ∅ (DeterministicSigning.memoize computation ∅) := by
    simpa only [QueryCache.empty_apply, ne_eq, not_true_eq_false, Set.setOf_false] using
      DeterministicSigning.freshRequests_memoize computation ∅
  apply referencePhaseCost_le_of_table secretKey _ hfresh.withRequestLog (cache, 0) q
    (fun randomizers => tablePhaseCostBound_logged_memoize randomizers secretKey
      computation cache q (hbound randomizers)) result hresult

/-- info: 'XmssSecurity.TargetSum.Seeded.tablePhaseCostBound_of_seed_caches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tablePhaseCostBound_of_seed_caches

/-- info: 'XmssSecurity.TargetSum.Seeded.tablePhaseCostBound_memoize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tablePhaseCostBound_memoize

/-- info: 'XmssSecurity.TargetSum.Seeded.referencePhaseCost_logged_memo_le_of_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms referencePhaseCost_logged_memo_le_of_table

end XmssSecurity.TargetSum.Seeded
