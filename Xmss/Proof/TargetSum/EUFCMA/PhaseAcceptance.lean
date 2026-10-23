import Xmss.Proof.TargetSum.EUFCMA.FreshAcceptance
import Xmss.Proof.TargetSum.Direct.DecidingSecondLaneAccepted
import Xmss.Proof.TargetSum.ExpectedQueryProjection
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.CacheDecode
import Xmss.Proof.TargetSum.EncodingProbability

/-! Transfer the direct-encoding acceptance estimate to the ordinary logged
adversary phase, where the deciding-path collision analysis is performed. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace Xmss.TargetSum.EUFCMA
open Xmss.EUFCMA

open Hashing Wots Merkle Verify Keygen Signing Generic.CappedExecution Deciding

def HasFreshAcceptedEncodingInLog (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (log : QueryLog Generic.SigningSpec) : Prop :=
  ∃ forgery : Generic.Forgery, ∃ output : Digest,
    ¬ Unforgeability.SigningTranscript.ContainsRequest log forgery ∧
    cache (Generic.CacheView.encodingInput parameter forgery.epoch
      (forgery.message, forgery.signature.randomness)) = some output ∧
    Generic.Code.ValidDigest (output)

theorem sourceDirectTraced_log_projection (publicKey : PublicKey) (secretKey : Generic.SecretKey)
    {α : Type} (computation : OracleComp (OracleWorld + Generic.SigningSpec) α)
    (cache : QueryCache HashSpec) (trace : Generic.AttackerActionTrace) :
    Prod.map id (fun state : Generic.CappedExecution.SourceTracedState => (state.1, state.2.toSigningLog)) <$>
      (simulateQ (Generic.CappedExecution.sourceDirectTracedMappedAdversaryImpl publicKey secretKey) computation).run (cache, trace) =
      (simulateQ (Generic.cappedLogTracedMappedAdversaryImpl publicKey secretKey) computation).run
        (cache, Generic.CappedExecution.AttackerActionTrace.toSigningLog trace) := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (Generic.CappedExecution.sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
    (Generic.cappedLogTracedMappedAdversaryImpl publicKey secretKey)
    (fun state : Generic.CappedExecution.SourceTracedState => (state.1, state.2.toSigningLog))
  intro input state
  simp only [Generic.CappedExecution.sourceDirectTracedMappedAdversaryImpl, Generic.CappedExecution.actionTracedStateImpl, StateT.run_mk,
    Generic.cappedLogTracedMappedAdversaryImpl, QueryImpl.extendState_apply, map_bind]
  apply bind_congr
  intro result
  simp only [map_pure, Prod.map_apply, id_eq, Generic.CappedExecution.AttackerActionTrace.toSigningLog_append,
    Generic.CappedExecution.attackerActionFragment_toSigningLog, Generic.signingLogUpdate]

theorem sourceDirectTraced_log_projection_eq_phase (adversary : Generic.Adversary)
    (publicKey : PublicKey) (secretKey : Generic.SecretKey) (cache : QueryCache HashSpec) :
    Prod.map id (fun state : Generic.CappedExecution.SourceTracedState => (state.1, state.2.toSigningLog)) <$>
      (simulateQ (Generic.CappedExecution.sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
        (adversary.main publicKey)).run (cache, []) =
      (fun result => (result.1.1, (result.2, result.1.2))) <$>
        (simulateQ Generic.romImpl (Generic.Deciding.adversaryPhase adversary publicKey secretKey)).run cache := by
  rw [sourceDirectTraced_log_projection]
  change (simulateQ (Generic.cappedLogTracedMappedAdversaryImpl publicKey secretKey)
    (adversary.main publicKey)).run (cache, []) = _
  rw [← Generic.cappedSelectivelyLoggedMappedAdversaryImpl_run_eq_logTraced publicKey secretKey
    (adversary.main publicKey) cache [], Generic.cappedSelectivelyLoggedMappedAdversaryImpl_eq_mapped]
  rw [Generic.cappedMappedAdversaryImpl, ← QueryImpl.simulateQ_writerTMapBase_run]
  rfl

theorem expected_directEncoding_forget_trace (publicKey : PublicKey) (secretKey : Generic.SecretKey)
    {α : Type} (computation : OracleComp (OracleWorld + Generic.SigningSpec) α)
    (cache : QueryCache HashSpec) (trace : Generic.AttackerActionTrace) :
    expectedSimulatedQueryCount (Generic.CappedExecution.sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
      (IsDirectEncodingQuery secretKey.parameter) computation (cache, trace) =
    expectedSimulatedQueryCount (Generic.cappedUnloggedMappedAdversaryImpl publicKey secretKey)
      (Generic.Direct.IsDirectEncodingQuery secretKey.parameter) computation cache := by
  have hproj := expectedSimulatedQueryCount_eq_of_query_map_eq
    (Generic.CappedExecution.sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
    (Generic.cappedUnloggedMappedAdversaryImpl publicKey secretKey) Prod.fst
    (by
      intro input state
      simp only [Generic.CappedExecution.sourceDirectTracedMappedAdversaryImpl, Generic.CappedExecution.actionTracedStateImpl, StateT.run_mk,
        map_bind, map_pure, Prod.map_apply, id_eq]
      change ((Generic.CappedExecution.sourceDirectMappedAdversaryImpl publicKey secretKey input).run state.1 >>= pure) = _
      rw [bind_pure]
      cases input <;> rfl)
    (IsDirectEncodingQuery secretKey.parameter) computation (cache, trace)
  rw [hproj]
  congr 1
  funext input
  rcases input with (uniformInput | hashInput) | request <;> rfl

theorem freshAccepted_adversaryPhase_le_expectedDirect (adversary : Generic.Adversary)
    (publicKey : PublicKey) (secretKey : Generic.SecretKey) (cache : QueryCache HashSpec)
    (hempty : ∀ leaf payload, cache (Generic.CacheView.encodingInput secretKey.parameter leaf payload) = none) :
    Pr[fun result => HasFreshAcceptedEncodingInLog secretKey.parameter result.2 result.1.2 |
      (simulateQ Generic.romImpl (Generic.Deciding.adversaryPhase adversary publicKey secretKey)).run cache] ≤
      TargetSum.acceptanceProbability *
        expectedSimulatedQueryCount (Generic.cappedUnloggedMappedAdversaryImpl publicKey secretKey)
          (Generic.Direct.IsDirectEncodingQuery secretKey.parameter) (adversary.main publicKey) cache := by
  have hbound := probEvent_freshAccepted_le_expected_directEncoding publicKey secretKey
    (adversary.main publicKey) (cache, [])
    (no_freshAcceptedEncoding_of_no_encodingInputs _ _ _ hempty)
  rw [expected_directEncoding_forget_trace] at hbound
  have heq := congrArg (fun computation => Pr[fun result : Generic.Forgery × (QueryCache HashSpec × QueryLog Generic.SigningSpec) =>
    HasFreshAcceptedEncodingInLog secretKey.parameter result.2.1 result.2.2 | computation])
    (sourceDirectTraced_log_projection_eq_phase adversary publicKey secretKey cache)
  simp only [probEvent_map] at heq
  exact heq ▸ hbound

theorem winning_verification_hasFreshAcceptedEncoding_at_prefix (adversary : Generic.Adversary)
    (keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ Generic.romImpl Generic.precomputedScheme.keygen).run ∅))
    (prefixResult : (Generic.Forgery × QueryLog Generic.SigningSpec) × QueryCache HashSpec)
    (hprefix : prefixResult ∈ support ((simulateQ Generic.romImpl
      (Generic.Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run keyResult.2))
    (hcached : prefixResult.2 (Generic.CacheView.encodingInput keyResult.1.2.parameter
      prefixResult.1.1.epoch (prefixResult.1.1.message, prefixResult.1.1.signature.randomness)) ≠ none)
    (execution : Generic.GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support ((simulateQ Generic.romImpl
      (Generic.Deciding.verificationPhase keyResult.1.1 keyResult.1.2 prefixResult.1)).run prefixResult.2))
    (hwin : standardWon execution.1 = true) :
    HasFreshAcceptedEncodingInLog keyResult.1.2.parameter prefixResult.2 prefixResult.1.2 := by
  have hstrong := strongWon_of_standardWon execution.1 hwin
  have hfull := Generic.Deciding.afterKeygen_of_phases adversary keyResult.1.1 keyResult.1.2 keyResult.2
    prefixResult hprefix execution hafter
  have hgame := Generic.CappedLeaf.afterKeygen_execution_mem_detailedGame adversary keyResult hkey execution hfull
  obtain ⟨event, hevent⟩ := Generic.winning_outcome_has_badEvent execution.2 execution.1
    (Generic.capped_detailed_execution_consistent adversary execution hgame) hstrong
  obtain ⟨encoding, hdecoded⟩ := Generic.WinningOutcomeBadEventOccurs.forgery_decode ⟨hstrong, hevent⟩
  have hdecode := Generic.CacheView.decodeDigest_of_decodedEncoding hdecoded
  have hfields := Generic.Deciding.verificationPhase_support _ _ _ _ _ hafter
  have hfresh := (standardWon_eq_true_iff _).1 hwin |>.2.1
  rw [hfields.2.1, hfields.2.2.1] at hdecode
  rw [hfields.2.2.1, hfields.2.2.2.1] at hfresh
  rw [← Generic.Deciding.encodingHash_eq_of_cached prefixResult.2 execution.2
    (Generic.xmssRom_cache_le _ prefixResult.2 execution hafter) _ _ _ hcached] at hdecode
  obtain ⟨output, houtput⟩ := TargetSum.encodingInput_cached_of_decode_some prefixResult.2
    keyResult.1.2.parameter prefixResult.1.1.epoch prefixResult.1.1.message
    prefixResult.1.1.signature.randomness encoding hdecode
  refine ⟨prefixResult.1.1, output, hfresh, houtput, encoding, ?_⟩
  simpa [Generic.CacheView.encodingHash, Generic.CacheView.digestAt, houtput] using hdecode

/-- info: 'Xmss.TargetSum.EUFCMA.freshAccepted_adversaryPhase_le_expectedDirect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms freshAccepted_adversaryPhase_le_expectedDirect

end Xmss.TargetSum.EUFCMA
