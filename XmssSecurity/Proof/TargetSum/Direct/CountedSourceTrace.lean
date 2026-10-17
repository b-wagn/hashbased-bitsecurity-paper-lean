import XmssSecurity.Proof.TargetSum.Deterministic.PhaseCounts
import XmssSecurity.Proof.TargetSum.CappedExactFirstLaneSourceCoupling

/-! Retain direct and signer counts in the source experiment used by the first-lane
coupling. Forgetting the counters gives exactly the existing traced source experiment. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.CappedChain

open Seeded

noncomputable def unloggedPhaseImpl
    (signing : SignRequest → OracleComp OracleWorld (Option Signature)) :
    QueryImpl (OracleWorld + SigningSpec) (StateT (QueryCache HashSpec) ProbComp) :=
  romImpl + fun request => simulateQ romImpl (signing request)

theorem phaseCountsImpl_cache_query_projection
    (signing : SignRequest → OracleComp OracleWorld (Option Signature))
    (input : (OracleWorld + SigningSpec).Domain) (state : PhaseCounts) :
    (fun result => (result.1, result.2.cache)) <$>
      (phaseCountsImpl signing input).run state =
        (unloggedPhaseImpl signing input).run state.cache := by
  cases input with
  | inl input =>
      simp only [phaseCountsImpl, StateT.run, Functor.map_map]
      exact id_map _
  | inr request =>
      simp only [phaseCountsImpl, StateT.run, Functor.map_map]
      change (fun result => (result.1.1, result.2)) <$>
        (simulateQ romImpl (countHashQueries (signing request))).run state.cache =
          (simulateQ romImpl (signing request)).run state.cache
      exact countHashQueries_run_forget (signing request) state.cache

structure CountedSourceState where
  counts : PhaseCounts
  signingTrace : SigningCacheTrace
  encodingTrace : EncodingActionTrace
  attackerTrace : AttackerActionTrace

def CountedSourceState.initial (cache : QueryCache HashSpec) : CountedSourceState :=
  ⟨⟨cache, 0, 0⟩, [], [], []⟩

def CountedSourceState.toSource (state : CountedSourceState) : SourceExactTracedState :=
  (((state.counts.cache, state.signingTrace), state.encodingTrace), state.attackerTrace)

noncomputable def countedSourceUpdate (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (initial : CountedSourceState)
    (answer : (OracleWorld + SigningSpec).Range input) (counts : PhaseCounts) : CountedSourceState :=
  let signingTrace := signingCacheTraceUpdate input initial.counts.cache answer counts.cache
    initial.signingTrace
  ⟨counts, signingTrace,
    encodingActionTraceUpdate secretKey input (initial.counts.cache, initial.signingTrace)
      answer (counts.cache, signingTrace) initial.encodingTrace,
    initial.attackerTrace ++ attackerActionFragment input answer⟩

noncomputable def countedSourceImpl (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec) (StateT CountedSourceState ProbComp) := fun input state =>
  (fun result => (result.1, countedSourceUpdate secretKey input state result.1 result.2)) <$>
    (referencePhaseCountsImpl secretKey input).run state.counts

theorem countedSourceImpl_counts_projection (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (state : CountedSourceState) :
    Prod.map id CountedSourceState.counts <$> (countedSourceImpl secretKey input).run state =
      (referencePhaseCountsImpl secretKey input).run state.counts := by
  simp only [countedSourceImpl, StateT.run, Functor.map_map]
  exact id_map _

theorem countedSource_counts_projection {α : Type} (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CountedSourceState) :
    Prod.map id CountedSourceState.counts <$>
      (simulateQ (countedSourceImpl secretKey) computation).run state =
        (simulateQ (referencePhaseCountsImpl secretKey) computation).run state.counts :=
  map_run_simulateQ_eq_of_query_map_eq _ _ _
    (countedSourceImpl_counts_projection secretKey) computation state

theorem countedSourceImpl_source_projection (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (state : CountedSourceState) :
    Prod.map id CountedSourceState.toSource <$> (countedSourceImpl secretKey input).run state =
      (cappedBothTracedMappedAdversaryImpl publicKey secretKey input).run state.toSource := by
  have hbase : (fun result => (result.1, result.2.cache)) <$>
      (referencePhaseCountsImpl secretKey input).run state.counts =
        (cappedUnloggedMappedAdversaryImpl publicKey secretKey input).run state.counts.cache := by
    have h := phaseCountsImpl_cache_query_projection
      (fun (request : SignRequest) =>
        Concrete.precomputedCappedSign secretKey request.epoch request.message) input state.counts
    cases input <;> exact h
  unfold cappedBothTracedMappedAdversaryImpl cappedEncodingTracedMappedAdversaryImpl
    cappedCacheTracedMappedAdversaryImpl
  simp only [QueryImpl.extendState_apply, bind_pure_comp, Functor.map_map]
  dsimp only [CountedSourceState.toSource]
  rw [← hbase]
  simp only [countedSourceImpl, StateT.run, Functor.map_map]
  rfl

theorem countedSource_source_projection {α : Type} (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CountedSourceState) :
    Prod.map id CountedSourceState.toSource <$>
      (simulateQ (countedSourceImpl secretKey) computation).run state =
        (simulateQ (cappedBothTracedMappedAdversaryImpl publicKey secretKey) computation).run
          state.toSource :=
  map_run_simulateQ_eq_of_query_map_eq _ _ _
    (countedSourceImpl_source_projection publicKey secretKey) computation state

/-- info: 'XmssSecurity.TargetSum.CappedChain.countedSource_source_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms countedSource_source_projection

end XmssSecurity.TargetSum.CappedChain
