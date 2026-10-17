import XmssSecurity.Proof.TargetSum.Seeded.HashTrace
import XmssSecurity.Proof.TargetSum.ExpectedCountedQueries

/-! Filtered hash traces record exactly the selected-query instrumentation, including
repeated queries. This identity keeps expected seed-guessing costs on their own tags. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Seeded

theorem traceHashes_filter_length {α : Type} (selected : HashInput → Prop) [DecidablePred selected]
    (computation : OracleComp OracleWorld α) :
    (fun result => (result.1, (result.2.filter (fun input => decide (selected input))).length)) <$>
      traceHashes computation = QueryCounting.counted (hashBad selected) computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      simp only [traceHashes_query_bind, QueryCounting.counted_query_bind, map_bind, map_pure]
      congr 1
      funext answer
      rw [← ih answer]
      simp only [bind_pure_comp, Functor.map_map]
      congr 1
      funext result
      cases input with
      | inl n => simp [prependHash, hashBad]
      | inr input =>
          by_cases h : selected input <;> simp [prependHash, hashBad, h, Nat.add_comm]

theorem expectedHashQueries_eq_filtered_trace {α : Type}
    (selected : HashInput → Prop) [DecidablePred selected]
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    expectedSimulatedQueryCount romImpl (hashBad selected) computation cache =
      ∑' result, Pr[= result | (simulateQ romImpl (traceHashes computation)).run' cache] *
        ((result.2.filter (fun input => decide (selected input))).length : ℝ≥0∞) := by
  rw [expectedSimulatedQueryCount_eq_counted, ← traceHashes_filter_length selected computation]
  simp only [simulateQ_map, StateT.run_map, tsum_probOutput_map_mul,
    StateT.run'_eq]

/-- info: 'XmssSecurity.TargetSum.Seeded.expectedHashQueries_eq_filtered_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms expectedHashQueries_eq_filtered_trace

end XmssSecurity.TargetSum.Seeded
