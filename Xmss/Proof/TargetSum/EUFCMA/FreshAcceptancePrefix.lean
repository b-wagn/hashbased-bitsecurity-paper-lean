import Xmss.Proof.TargetSum.EUFCMA.FreshAcceptance
import Xmss.Proof.TargetSum.EUFCMA.FreshEncodingPrefix
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! The fresh-encoding acceptance estimate on the source prefix used in the
deciding-chain proof, retaining the ordinary direct-query budget. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum.EUFCMA
open Xmss.EUFCMA

open Hashing Wots Merkle Verify Keygen Signing CappedExecution Deciding

def SourcePrefixFreshAccepted (key : CappedExecution.ProgrammedGlobalChainKeygenView)
    (result : Forgery × CappedExecution.SourceExactTracedState) : Prop :=
  ¬ Unforgeability.SigningTranscript.ContainsRequest result.2.2.toSigningLog result.1 ∧
    ∃ encoding, Code.decodeDigest (CacheView.encodingHash result.2.1.1.1 key.secretKey.parameter
      result.1.epoch (result.1.message, result.1.signature.randomness)) = some encoding

theorem sourcePrefix_freshAccepted_probability_le (adversary : Adversary)
    (key : CappedExecution.ProgrammedGlobalChainKeygenView)
    (hkey : key ∈ support CappedExecution.trajectoryProgrammedGlobalChainKeygen)
    (D : ℕ) (hD : Direct.IsDirectQueryBound adversary D) :
    Pr[SourcePrefixFreshAccepted key | Deciding.sourcePrefixExecution adversary key] ≤
      TargetSum.acceptanceProbability * (D : ℝ≥0∞) := by
  have hbound := probEvent_freshAccepted_le_direct_budget key.publicKey
    (Keygen.materializePrecomputation key.cache key.secretKey) (adversary.main key.publicKey) key.cache
    (by
      rw [Keygen.materializePrecomputation_parameter]
      exact Keygen.keygen_cache_none_encodingInput key.keyResult
        (CappedExecution.trajectoryProgrammedGlobalChainKeygen_support_keyResult key hkey)) D (hD key.publicKey)
  rw [Keygen.materializePrecomputation_parameter] at hbound
  rw [← CappedExecution.cappedBothTracedMappedAdversaryImpl_actionProjection key.publicKey
    (Keygen.materializePrecomputation key.cache key.secretKey)
    (adversary.main key.publicKey) ((key.cache, []), []) [], probEvent_map] at hbound
  apply le_trans _ hbound
  apply probEvent_mono''
  rintro result ⟨hfresh, encoding, hdecode⟩
  exact hasFreshAcceptedEncoding_of_decode key.secretKey.parameter
    (result.2.1.1.1, result.2.2) result.1 encoding hfresh hdecode

/-- info: 'Xmss.TargetSum.EUFCMA.sourcePrefix_freshAccepted_probability_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sourcePrefix_freshAccepted_probability_le

end Xmss.TargetSum.EUFCMA
