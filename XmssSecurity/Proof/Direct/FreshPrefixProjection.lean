import XmssSecurity.Proof.Direct.DecidingSecondLaneFresh
import XmssSecurity.Proof.Direct.FreshVerificationProbability
import XmssSecurity.Proof.Direct.LimitedAcceptanceCancellation

/-! Freshness is the same event in the standard reference prefix and the traced
source prefix. Both lanes can therefore retain one common fresh-encoding probability. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.Deciding

open CappedChain Direct

theorem adversaryPhase_cache_projection (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : SecretKey) (cache : QueryCache HashSpec) :
    (fun result : (Forgery × QueryLog SigningSpec) × QueryCache HashSpec => (result.1.1, result.2)) <$>
      (simulateQ romImpl (adversaryPhase adversary publicKey secretKey)).run cache =
        (simulateQ (cappedUnloggedMappedAdversaryImpl publicKey secretKey)
          (adversary.main publicKey)).run cache := by
  have hproject := QueryImpl.fst_map_run_withTraceAppend
    (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey) signingLogFragment
    (adversary.main publicKey)
  rw [cappedSourceUnloggedMappedAdversaryImpl_withTraceAppend_eq] at hproject
  rw [CappedEncodingMonitor.cappedUnloggedMappedAdversary_simulateQ_run_eq_source,
    ← hproject, simulateQ_map, StateT.run_map]
  rfl

theorem countedSource_fresh_probability_eq_reference (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : SecretKey) (cache : QueryCache HashSpec) :
    Pr[fun result : Forgery × CountedSourceState =>
        result.2.counts.cache (forgeryEncodingInput publicKey result.1) = none |
      (simulateQ (countedSourceImpl secretKey) (adversary.main publicKey)).run (CountedSourceState.initial cache)] =
    Pr[fun result => result.2 (forgeryEncodingInput publicKey result.1.1) = none |
      (simulateQ romImpl (adversaryPhase adversary publicKey secretKey)).run cache] := by
  have hcount := countedSource_cache_projection publicKey secretKey (adversary.main publicKey)
    (CountedSourceState.initial cache)
  have hphase := adversaryPhase_cache_projection adversary publicKey secretKey cache
  have heq := congrArg (fun computation : ProbComp (Forgery × QueryCache HashSpec) =>
    Pr[fun result => result.2 (forgeryEncodingInput publicKey result.1) = none | computation])
      (hcount.trans hphase.symm)
  simpa only [probEvent_map, Function.comp_def] using heq

theorem sourcePrefix_fresh_probability_eq_reference (adversary : Adversary)
    (key : ProgrammedGlobalChainKeygenView) :
    Pr[fun result => SourcePrefixForgedEncodingFresh (key, result) | sourcePrefixExecution adversary key] =
      Pr[fun result => result.2 (forgeryEncodingInput key.publicKey result.1.1) = none |
        (simulateQ romImpl (adversaryPhase adversary key.publicKey
          (Concrete.materializePrecomputation key.cache key.secretKey))).run key.cache] := by
  have hproject := countedSource_source_projection key.publicKey
    (Concrete.materializePrecomputation key.cache key.secretKey) (adversary.main key.publicKey)
    (CountedSourceState.initial key.cache)
  change Prod.map id CountedSourceState.toSource <$> sourceCountedPrefixExecution adversary key =
    sourcePrefixExecution adversary key at hproject
  rw [← hproject, probEvent_map]
  exact countedSource_fresh_probability_eq_reference adversary key.publicKey
    (Concrete.materializePrecomputation key.cache key.secretKey) key.cache

theorem forgedEncodingFreshProbability_eq_source (adversary : Adversary) :
    forgedEncodingFreshProbability adversary =
      Pr[SourcePrefixForgedEncodingFresh | sourcePrefixProgram adversary] := by
  let fresh := fun keyResult : (PublicKey × SecretKey) × QueryCache HashSpec =>
    Pr[fun result => result.2 (forgeryEncodingInput keyResult.1.1 result.1.1) = none |
      (simulateQ romImpl (adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run keyResult.2]
  symm
  unfold sourcePrefixProgram
  rw [probEvent_bind_eq_tsum]
  simp only [bind_pure_comp, probEvent_map, Function.comp_def]
  simp_rw [sourcePrefix_fresh_probability_eq_reference]
  change (∑' key, Pr[= key | trajectoryProgrammedGlobalChainKeygen] *
    fresh (Concrete.materializeCachedKeyResult key.keyResult)) = _
  calc
    _ = ∑' keyResult, Pr[= keyResult | (fun key : ProgrammedGlobalChainKeygenView =>
        Concrete.materializeCachedKeyResult key.keyResult) <$> trajectoryProgrammedGlobalChainKeygen] *
          fresh keyResult := by rw [tsum_probOutput_map_mul]
    _ = _ := by
      apply tsum_congr
      intro keyResult
      rw [probOutput_congr rfl evalDist_materializedTrajectoryGlobalChainKeygen_eq_cappedKeygen]

/-- info: 'XmssSecurity.Deciding.forgedEncodingFreshProbability_eq_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forgedEncodingFreshProbability_eq_source

end XmssSecurity.Deciding
