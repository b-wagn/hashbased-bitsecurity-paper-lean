import VCVio.OracleComp.QueryTracking.Tracing
import VCVio.OracleComp.SimSemantics.StateT.Basic

/-!
# Traces of simulated computations

Generic facts about query implementations that append to a trace: an implementation whose
trace is constantly empty, a projection of the trace that commutes with every query, and a
stateful handler whose trace is a function of its state.
-/

open OracleComp OracleSpec ENNReal

namespace QueryImpl

@[simp] theorem run_simulateQ_withTraceAppend_const_empty
    {spec : OracleSpec ι} {m : Type → Type*} [Monad m] [LawfulMonad m] {Log : Type}
    [EmptyCollection Log] [Append Log] [LawfulAppend Log]
    (impl : QueryImpl spec m) (computation : OracleComp spec α) :
    (simulateQ (impl.withTraceAppend (fun _ _ => (∅ : Log))) computation).run =
      (fun result => (result, ∅)) <$> simulateQ impl computation := by
  induction computation using OracleComp.inductionOn <;> simp [*]

theorem mapLog_run_simulateQ_of_query
    {SourceLog TargetLog : Type}
    [EmptyCollection SourceLog] [Append SourceLog] [LawfulAppend SourceLog]
    [EmptyCollection TargetLog] [Append TargetLog] [LawfulAppend TargetLog]
    (source : QueryImpl spec (WriterT SourceLog ProbComp))
    (target : QueryImpl spec (WriterT TargetLog ProbComp))
    (project : SourceLog → TargetLog)
    (h_empty : project ∅ = ∅)
    (h_append : ∀ left right,
      project (left ++ right) = project left ++ project right)
    (hquery : ∀ input,
      Prod.map id project <$> (source input).run = (target input).run)
    (computation : OracleComp spec α) :
    Prod.map id project <$> (simulateQ source computation).run =
      (simulateQ target computation).run := by
  induction computation using OracleComp.inductionOn with
  | pure result => simp [h_empty]
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
        OracleQuery.input_query, id_map, WriterT.run_bind', map_bind]
      rw [← hquery input, bind_map_left]
      apply bind_congr
      intro result
      simp only [Prod.map, id_eq]
      rw [← ih result.1]
      simp [h_append, Prod.map]


theorem simulateQ_stateHandler_trace
    {ι : Type} {spec : OracleSpec ι}
    {Log State : Type}
    [EmptyCollection Log] [Append Log] [LawfulAppend Log]
    (eager : QueryImpl spec (WriterT Log ProbComp))
    (handler : QueryImpl spec (StateT State (OracleComp spec)))
    (advance : State → Log → State)
    (project : State → Log → Log)
    (advance_empty : ∀ state, advance state ∅ = state)
    (advance_append : ∀ state left right,
      advance state (left ++ right) = advance (advance state left) right)
    (project_empty : ∀ state, project state ∅ = ∅)
    (project_append : ∀ state left right,
      project state (left ++ right) =
        project state left ++ project (advance state left) right)
    (hquery : ∀ input state,
      (simulateQ eager ((handler input).run state)).run =
        (fun result =>
          ((result.1, advance state result.2), project state result.2)) <$>
          (simulateQ eager (liftM (spec.query input))).run)
    (computation : OracleComp spec α) (state : State) :
    (simulateQ eager ((simulateQ handler computation).run state)).run =
      (fun result =>
        ((result.1, advance state result.2), project state result.2)) <$>
        (simulateQ eager computation).run := by
  rw [QueryImpl.simulateQ_mapStateTBase_run]
  induction computation using OracleComp.inductionOn generalizing state with
  | pure result => simp [advance_empty, project_empty]
  | query_bind input next ih =>
      rw [simulateQ_query_bind, StateT.run_bind]
      rw [simulateQ_bind, WriterT.run_bind']
      change (do
        let head ← (simulateQ eager ((handler input).run state)).run
        (Prod.map id fun tail => head.2 ++ tail) <$>
          ((simulateQ (eager.mapStateTBase handler) (next head.1.1)).run
            head.1.2).run) = _
      rw [hquery input state]
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply]
      rw [WriterT.run_bind']
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply]
      apply bind_congr
      intro head
      rw [ih head.1 (advance state head.2)]
      simp [advance_append, project_append, Prod.map]

end QueryImpl
