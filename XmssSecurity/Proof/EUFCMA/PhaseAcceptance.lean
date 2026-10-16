import XmssSecurity.Proof.EUFCMA.FreshAcceptance
import XmssSecurity.Proof.Direct.DecidingSecondLaneAccepted
import XmssSecurity.Proof.ExpectedQueryProjection

/-! Transfer the direct-encoding acceptance estimate to the ordinary logged
adversary phase, where the deciding-path collision analysis is performed. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.EUFCMA

open Concrete CappedChain Deciding

def HasFreshAcceptedEncodingInLog (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) : Prop :=
  ∃ forgery : Forgery, ∃ output : HashOutput,
    ¬ SigningTranscript.ContainsRequest log forgery ∧
    cache (CacheView.encodingInput parameter forgery.epoch
      (forgery.message, forgery.signature.randomness)) = some output ∧
    Checksum.ValidDigest (truncateHash output)

theorem sourceDirectTraced_log_projection (publicKey : PublicKey) (secretKey : SecretKey)
    {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) (trace : AttackerActionTrace) :
    Prod.map id (fun state : SourceTracedState => (state.1, state.2.toSigningLog)) <$>
      (simulateQ (sourceDirectTracedMappedAdversaryImpl publicKey secretKey) computation).run (cache, trace) =
      (simulateQ (cappedLogTracedMappedAdversaryImpl publicKey secretKey) computation).run
        (cache, AttackerActionTrace.toSigningLog trace) := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
    (cappedLogTracedMappedAdversaryImpl publicKey secretKey)
    (fun state : SourceTracedState => (state.1, state.2.toSigningLog))
  intro input state
  simp only [sourceDirectTracedMappedAdversaryImpl, actionTracedStateImpl, StateT.run_mk,
    cappedLogTracedMappedAdversaryImpl, QueryImpl.extendState_apply, map_bind]
  apply bind_congr
  intro result
  simp only [map_pure, Prod.map_apply, id_eq, AttackerActionTrace.toSigningLog_append,
    attackerActionFragment_toSigningLog, signingLogUpdate]

theorem sourceDirectTraced_log_projection_eq_phase (adversary : XmssSecurity.Adversary)
    (publicKey : PublicKey) (secretKey : SecretKey) (cache : QueryCache HashSpec) :
    Prod.map id (fun state : SourceTracedState => (state.1, state.2.toSigningLog)) <$>
      (simulateQ (sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
        (adversary.main publicKey)).run (cache, []) =
      (fun result => (result.1.1, (result.2, result.1.2))) <$>
        (simulateQ romImpl (adversaryPhase adversary publicKey secretKey)).run cache := by
  rw [sourceDirectTraced_log_projection]
  change (simulateQ (cappedLogTracedMappedAdversaryImpl publicKey secretKey)
    (adversary.main publicKey)).run (cache, []) = _
  rw [← cappedSelectivelyLoggedMappedAdversaryImpl_run_eq_logTraced publicKey secretKey
    (adversary.main publicKey) cache [], cappedSelectivelyLoggedMappedAdversaryImpl_eq_mapped]
  rw [cappedMappedAdversaryImpl, ← QueryImpl.simulateQ_writerTMapBase_run]
  rfl

theorem expected_directEncoding_forget_trace (publicKey : PublicKey) (secretKey : SecretKey)
    {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) (trace : AttackerActionTrace) :
    expectedSimulatedQueryCount (sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
      (IsDirectEncodingQuery secretKey.parameter) computation (cache, trace) =
    expectedSimulatedQueryCount (cappedUnloggedMappedAdversaryImpl publicKey secretKey)
      (Direct.IsDirectEncodingQuery secretKey.parameter) computation cache := by
  have hproj := expectedSimulatedQueryCount_eq_of_query_map_eq
    (sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
    (cappedUnloggedMappedAdversaryImpl publicKey secretKey) Prod.fst
    (by
      intro input state
      simp only [sourceDirectTracedMappedAdversaryImpl, actionTracedStateImpl, StateT.run_mk,
        map_bind, map_pure, Prod.map_apply, id_eq]
      change ((sourceDirectMappedAdversaryImpl publicKey secretKey input).run state.1 >>= pure) = _
      rw [bind_pure]
      cases input <;> rfl)
    (IsDirectEncodingQuery secretKey.parameter) computation (cache, trace)
  rw [hproj]
  congr 1
  funext input
  rcases input with (uniformInput | hashInput) | request <;> rfl

theorem freshAccepted_adversaryPhase_le_expectedDirect (adversary : XmssSecurity.Adversary)
    (publicKey : PublicKey) (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (hempty : ∀ leaf payload, cache (CacheView.encodingInput secretKey.parameter leaf payload) = none) :
    Pr[fun result => HasFreshAcceptedEncodingInLog secretKey.parameter result.2 result.1.2 |
      (simulateQ romImpl (adversaryPhase adversary publicKey secretKey)).run cache] ≤
      Checksum.acceptanceProbability *
        expectedSimulatedQueryCount (cappedUnloggedMappedAdversaryImpl publicKey secretKey)
          (Direct.IsDirectEncodingQuery secretKey.parameter) (adversary.main publicKey) cache := by
  have hbound := probEvent_freshAccepted_le_expected_directEncoding publicKey secretKey
    (adversary.main publicKey) (cache, [])
    (no_freshAcceptedEncoding_of_no_encodingInputs _ _ _ hempty)
  rw [expected_directEncoding_forget_trace] at hbound
  have heq := congrArg (fun computation => Pr[fun result : Forgery × (QueryCache HashSpec × QueryLog SigningSpec) =>
    HasFreshAcceptedEncodingInLog secretKey.parameter result.2.1 result.2.2 | computation])
    (sourceDirectTraced_log_projection_eq_phase adversary publicKey secretKey cache)
  simp only [probEvent_map] at heq
  exact heq ▸ hbound

theorem winning_verification_hasFreshAcceptedEncoding_at_prefix (adversary : XmssSecurity.Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (prefixResult : (Forgery × QueryLog SigningSpec) × QueryCache HashSpec)
    (hprefix : prefixResult ∈ support ((simulateQ romImpl
      (adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run keyResult.2))
    (hcached : prefixResult.2 (CacheView.encodingInput keyResult.1.2.parameter
      prefixResult.1.1.epoch (prefixResult.1.1.message, prefixResult.1.1.signature.randomness)) ≠ none)
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support ((simulateQ romImpl
      (verificationPhase keyResult.1.1 keyResult.1.2 prefixResult.1)).run prefixResult.2))
    (hwin : standardWon execution.1 = true) :
    HasFreshAcceptedEncodingInLog keyResult.1.2.parameter prefixResult.2 prefixResult.1.2 := by
  have hstrong := strongWon_of_standardWon execution.1 hwin
  have hfull := afterKeygen_of_phases adversary keyResult.1.1 keyResult.1.2 keyResult.2
    prefixResult hprefix execution hafter
  have hgame := CappedLeaf.afterKeygen_execution_mem_detailedGame adversary keyResult hkey execution hfull
  obtain ⟨event, hevent⟩ := winning_outcome_has_badEvent execution.2 execution.1
    (capped_detailed_execution_consistent adversary execution hgame) hstrong
  obtain ⟨encoding, hdecode⟩ := WinningOutcomeBadEventOccurs.forgery_decode ⟨hstrong, hevent⟩
  have hfields := verificationPhase_support _ _ _ _ _ hafter
  have hfresh := (standardWon_eq_true_iff _).1 hwin |>.2.1
  rw [hfields.2.1, hfields.2.2.1] at hdecode
  rw [hfields.2.2.1, hfields.2.2.2.1] at hfresh
  rw [← encodingHash_eq_of_cached prefixResult.2 execution.2
    (xmssRom_cache_le _ prefixResult.2 execution hafter) _ _ _ hcached] at hdecode
  obtain ⟨output, houtput⟩ := CacheView.encodingInput_cached_of_decode_some prefixResult.2
    keyResult.1.2.parameter prefixResult.1.1.epoch prefixResult.1.1.message
    prefixResult.1.1.signature.randomness encoding hdecode
  refine ⟨prefixResult.1.1, output, hfresh, houtput, encoding, ?_⟩
  simpa [CacheView.encodingHash, CacheView.digestAt, houtput] using hdecode

/-- info: 'XmssSecurity.EUFCMA.freshAccepted_adversaryPhase_le_expectedDirect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms freshAccepted_adversaryPhase_le_expectedDirect

end XmssSecurity.EUFCMA
