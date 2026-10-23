import Xmss.Proof.Generic.Seeded.CacheCoupling
import Xmss.Proof.Generic.ConsistentQueryBound

open OracleComp OracleSpec

namespace Xmss.Generic.Seeded

variable [Code]

set_option backward.isDefEq.respectTransparency false

def prependHash (input : OracleWorld.Domain) (inputs : List HashInput) : List HashInput :=
  match input with
  | .inl _ => inputs
  | .inr input => input :: inputs

noncomputable def traceHashes {α : Type} (computation : OracleComp OracleWorld α) :
    OracleComp OracleWorld (α × List HashInput) :=
  OracleComp.construct (fun value => pure (value, []))
    (fun input _ next => do
      let answer ← liftM (OracleWorld.query input)
      let result ← next answer
      return (result.1, prependHash input result.2)) computation

omit [Code] in
theorem traceHashes_pure {α : Type} (value : α) :
    traceHashes (pure value) = pure (value, []) := rfl

omit [Code] in
theorem traceHashes_query_bind {α : Type} (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld α) :
    traceHashes (liftM (OracleWorld.query input) >>= next) = (do
      let answer ← liftM (OracleWorld.query input)
      let result ← traceHashes (next answer)
      return (result.1, prependHash input result.2)) := rfl

def TraceHits (bad : HashInput → Prop) (inputs : List HashInput) : Prop :=
  ∃ input ∈ inputs, bad input

omit [Code] in
theorem traceHits_prepend (bad : HashInput → Prop) (input : OracleWorld.Domain)
    (inputs : List HashInput) :
    TraceHits bad (prependHash input inputs) ↔ hashBad bad input ∨ TraceHits bad inputs := by
  cases input <;> simp [TraceHits, prependHash, hashBad]

omit [Code] in
theorem probOutput_stopBefore_none {α : Type} (bad : HashInput → Prop) [DecidablePred bad]
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    Pr[= none | (simulateQ romImpl (stopBefore (hashBad bad) computation)).run' cache] =
      Pr[fun result => TraceHits bad result.2 |
        (simulateQ romImpl (traceHashes computation)).run' cache] := by
  classical
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp [stopBefore_pure, traceHashes_pure, TraceHits]
  | query_bind input next ih =>
      rw [stopBefore_query_bind, traceHashes_query_bind]
      by_cases hbad : hashBad bad input
      · rw [if_pos hbad, run'_query_bind]
        simp [bind_pure_comp, simulateQ_map, StateT.run'_eq, StateT.run_map]
        intro a b answer cache' _ a' inputs cache'' _ _ hb
        rw [← hb, traceHits_prepend]
        exact Or.inl hbad
      · rw [if_neg hbad, run'_query_bind, run'_query_bind]
        simp only [probOutput_bind_eq_tsum, probEvent_bind_eq_tsum]
        apply tsum_congr
        intro result
        rw [ih result.1 result.2]
        simp only [bind_pure_comp, simulateQ_map, StateT.run'_eq, StateT.run_map,
          Functor.map_map, probEvent_map, Function.comp_def, traceHits_prepend, hbad, false_or]

end Xmss.Generic.Seeded
