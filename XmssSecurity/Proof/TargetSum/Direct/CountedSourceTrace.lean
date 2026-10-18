import XmssSecurity.Proof.TargetSum.Deterministic.PhaseCounts
import XmssSecurity.Proof.Generic.CappedExactFirstLaneSourceCoupling
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability
/-! Retain direct and signer counts in the source experiment used by the first-lane
coupling. Forgetting the counters gives exactly the existing traced source experiment. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.CappedChain

open Seeded

noncomputable def unloggedPhaseImpl
    (signing : Generic.SignRequest → OracleComp OracleWorld (Option Generic.Signature)) :
    QueryImpl (OracleWorld + Generic.SigningSpec) (StateT (QueryCache HashSpec) ProbComp) :=
  Generic.romImpl + fun request => simulateQ Generic.romImpl (signing request)

theorem phaseCountsImpl_cache_query_projection
    (signing : Generic.SignRequest → OracleComp OracleWorld (Option Generic.Signature))
    (input : (OracleWorld + Generic.SigningSpec).Domain) (state : PhaseCounts) :
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
        (simulateQ Generic.romImpl (Generic.countHashQueries (signing request))).run state.cache =
          (simulateQ Generic.romImpl (signing request)).run state.cache
      exact Generic.countHashQueries_run_forget (signing request) state.cache

structure CountedSourceState where
  counts : PhaseCounts
  signingTrace : Generic.SigningCacheTrace
  encodingTrace : Generic.EncodingActionTrace
  attackerTrace : Generic.CappedChain.AttackerActionTrace

def CountedSourceState.initial (cache : QueryCache HashSpec) : CountedSourceState :=
  ⟨⟨cache, 0, 0⟩, [], [], []⟩

def CountedSourceState.toSource (state : CountedSourceState) : Generic.CappedChain.SourceExactTracedState :=
  (((state.counts.cache, state.signingTrace), state.encodingTrace), state.attackerTrace)

noncomputable def countedSourceUpdate (secretKey : Generic.SecretKey)
    (input : (OracleWorld + Generic.SigningSpec).Domain) (initial : CountedSourceState)
    (answer : (OracleWorld + Generic.SigningSpec).Range input) (counts : PhaseCounts) : CountedSourceState :=
  let signingTrace := Generic.signingCacheTraceUpdate input initial.counts.cache answer counts.cache
    initial.signingTrace
  ⟨counts, signingTrace,
    Generic.encodingActionTraceUpdate secretKey input (initial.counts.cache, initial.signingTrace)
      answer (counts.cache, signingTrace) initial.encodingTrace,
    initial.attackerTrace ++ Generic.CappedChain.attackerActionFragment input answer⟩

noncomputable def countedSourceImpl (secretKey : Generic.SecretKey) :
    QueryImpl (OracleWorld + Generic.SigningSpec) (StateT CountedSourceState ProbComp) := fun input state =>
  (fun result => (result.1, countedSourceUpdate secretKey input state result.1 result.2)) <$>
    (referencePhaseCountsImpl secretKey input).run state.counts

theorem countedSourceImpl_counts_projection (secretKey : Generic.SecretKey)
    (input : (OracleWorld + Generic.SigningSpec).Domain) (state : CountedSourceState) :
    Prod.map id CountedSourceState.counts <$> (countedSourceImpl secretKey input).run state =
      (referencePhaseCountsImpl secretKey input).run state.counts := by
  simp only [countedSourceImpl, StateT.run, Functor.map_map]
  exact id_map _

theorem countedSource_counts_projection {α : Type} (secretKey : Generic.SecretKey)
    (computation : OracleComp (OracleWorld + Generic.SigningSpec) α) (state : CountedSourceState) :
    Prod.map id CountedSourceState.counts <$>
      (simulateQ (countedSourceImpl secretKey) computation).run state =
        (simulateQ (referencePhaseCountsImpl secretKey) computation).run state.counts :=
  map_run_simulateQ_eq_of_query_map_eq _ _ _
    (countedSourceImpl_counts_projection secretKey) computation state

theorem countedSourceImpl_source_projection (publicKey : PublicKey) (secretKey : Generic.SecretKey)
    (input : (OracleWorld + Generic.SigningSpec).Domain) (state : CountedSourceState) :
    Prod.map id CountedSourceState.toSource <$> (countedSourceImpl secretKey input).run state =
      (Generic.CappedChain.cappedBothTracedMappedAdversaryImpl publicKey secretKey input).run state.toSource := by
  have hbase : (fun result => (result.1, result.2.cache)) <$>
      (referencePhaseCountsImpl secretKey input).run state.counts =
        (Generic.cappedUnloggedMappedAdversaryImpl publicKey secretKey input).run state.counts.cache := by
    have h := phaseCountsImpl_cache_query_projection
      (fun (request : Generic.SignRequest) =>
        Generic.Concrete.precomputedCappedSign secretKey request.epoch request.message) input state.counts
    cases input <;> exact h
  unfold Generic.CappedChain.cappedBothTracedMappedAdversaryImpl Generic.cappedEncodingTracedMappedAdversaryImpl
    Generic.cappedCacheTracedMappedAdversaryImpl
  simp only [QueryImpl.extendState_apply, bind_pure_comp, Functor.map_map]
  dsimp only [CountedSourceState.toSource]
  rw [← hbase]
  simp only [countedSourceImpl, StateT.run, Functor.map_map]
  rfl

theorem countedSource_source_projection {α : Type} (publicKey : PublicKey) (secretKey : Generic.SecretKey)
    (computation : OracleComp (OracleWorld + Generic.SigningSpec) α) (state : CountedSourceState) :
    Prod.map id CountedSourceState.toSource <$>
      (simulateQ (countedSourceImpl secretKey) computation).run state =
        (simulateQ (Generic.CappedChain.cappedBothTracedMappedAdversaryImpl publicKey secretKey) computation).run
          state.toSource :=
  map_run_simulateQ_eq_of_query_map_eq _ _ _
    (countedSourceImpl_source_projection publicKey secretKey) computation state

/-- info: 'XmssSecurity.TargetSum.CappedChain.countedSource_source_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms countedSource_source_projection

end XmssSecurity.TargetSum.CappedChain
