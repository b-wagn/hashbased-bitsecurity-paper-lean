import XmssSecurity.Proof.Generic.Seeded.HashTrace
import XmssSecurity.Proof.TargetSum.ExpectedCountedQueries
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Filtered hash traces record exactly the selected-query instrumentation, including
repeated queries. This identity keeps expected seed-guessing costs on their own tags. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.Seeded

theorem traceHashes_filter_length {α : Type} (selected : HashInput → Prop) [DecidablePred selected]
    (computation : OracleComp OracleWorld α) :
    (fun result => (result.1, (result.2.filter (fun input => decide (selected input))).length)) <$>
      Seeded.traceHashes computation = QueryCounting.counted (Seeded.hashBad selected) computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      simp only [Seeded.traceHashes_query_bind, QueryCounting.counted_query_bind, map_bind, map_pure]
      congr 1
      funext answer
      rw [← ih answer]
      simp only [bind_pure_comp, Functor.map_map]
      congr 1
      funext result
      cases input with
      | inl n => simp [Seeded.prependHash, Seeded.hashBad]
      | inr input =>
          by_cases h : selected input <;> simp [Seeded.prependHash, Seeded.hashBad, h, Nat.add_comm]

theorem expectedHashQueries_eq_filtered_trace {α : Type}
    (selected : HashInput → Prop) [DecidablePred selected]
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    expectedSimulatedQueryCount romImpl (Seeded.hashBad selected) computation cache =
      ∑' result, Pr[= result | (simulateQ romImpl (Seeded.traceHashes computation)).run' cache] *
        ((result.2.filter (fun input => decide (selected input))).length : ℝ≥0∞) := by
  rw [expectedSimulatedQueryCount_eq_counted, ← traceHashes_filter_length selected computation]
  simp only [simulateQ_map, StateT.run_map, tsum_probOutput_map_mul,
    StateT.run'_eq]

/-- info: 'XmssSecurity.TargetSum.Seeded.expectedHashQueries_eq_filtered_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms expectedHashQueries_eq_filtered_trace

end XmssSecurity.TargetSum.Seeded
