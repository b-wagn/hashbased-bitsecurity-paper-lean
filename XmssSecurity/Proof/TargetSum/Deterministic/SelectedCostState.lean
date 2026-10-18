import XmssSecurity.Proof.Generic.Deterministic.CostState
import XmssSecurity.Proof.TargetSum.ExpectedCountedQueries
import XmssSecurity.Proof.Generic.Seeded.CacheCoupling
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability
/-! Instrument a chosen hash domain in the state passed through distributional game
hops. Unlike the full hash counter, this counter leaves unrelated hash calls uncharged. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Seeded

noncomputable def selectedCostHash (selected : HashInput → Prop) [DecidablePred selected] :
    QueryImpl HashSpec (StateT Generic.Seeded.CostState ProbComp) := fun input state => do
  let result ← (randomOracle input).run state.1
  pure (result.1, result.2, state.2 + if selected input then 1 else 0)

theorem run_selectedCostQuery (selected : HashInput → Prop) [DecidablePred selected]
    (input : OracleWorld.Domain) (cache : QueryCache HashSpec) (cost : Nat) :
    ((Generic.Seeded.worldHandler (selectedCostHash selected)) input).run (cache, cost) =
      (fun result => (result.1, result.2, cost + if Generic.Seeded.hashBad selected input then 1 else 0)) <$>
        (Generic.romImpl input).run cache := by
  cases input with
  | inl input => simp [Generic.Seeded.worldHandler, Generic.Seeded.hashBad]; rfl
  | inr input =>
      change (do
        let result ← (randomOracle input).run cache
        pure (result.1, result.2, cost + if selected input then 1 else 0)) = _
      rw [bind_pure_comp]
      rfl

theorem run_selectedCostWorld {α : Type} (selected : HashInput → Prop) [DecidablePred selected]
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (cost : Nat) :
    (simulateQ (Generic.Seeded.worldHandler (selectedCostHash selected)) computation).run (cache, cost) =
      (fun result => (result.1.1, result.2, cost + result.1.2)) <$>
        (simulateQ Generic.romImpl (QueryCounting.counted (Generic.Seeded.hashBad selected) computation)).run cache := by
  induction computation using OracleComp.inductionOn generalizing cache cost with
  | pure value => simp only [simulateQ_pure, QueryCounting.counted_pure, StateT.run_pure, map_pure, Nat.add_zero]
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, QueryCounting.counted_query_bind,
        simulateQ_pure, StateT.run_pure, map_bind, run_selectedCostQuery, bind_map_left]
      apply bind_congr
      intro result
      rw [ih]
      simp only [map_pure, bind_pure_comp, Nat.add_assoc]

theorem expectedQueries_eq_selectedCostWorld {α : Type}
    (selected : HashInput → Prop) [DecidablePred selected]
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    expectedSimulatedQueryCount Generic.romImpl (Generic.Seeded.hashBad selected) computation cache =
      ∑' result, Pr[= result |
        (simulateQ (Generic.Seeded.worldHandler (selectedCostHash selected)) computation).run (cache, 0)] *
          (result.2.2 : ℝ≥0∞) := by
  rw [run_selectedCostWorld, tsum_probOutput_map_mul, expectedSimulatedQueryCount_eq_counted]
  simp only [Nat.zero_add]

/-- info: 'XmssSecurity.TargetSum.Seeded.expectedQueries_eq_selectedCostWorld' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms expectedQueries_eq_selectedCostWorld

end XmssSecurity.TargetSum.Seeded
