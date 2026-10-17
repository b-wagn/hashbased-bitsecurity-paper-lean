import XmssSecurity.Proof.TargetSum.EUFCMA.FreshAcceptance
import XmssSecurity.Proof.TargetSum.EUFCMA.FreshEncodingPrefix

/-! The fresh-encoding acceptance estimate on the source prefix used in the
deciding-chain proof, retaining the ordinary direct-query budget. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.EUFCMA
open XmssSecurity.EUFCMA

open Concrete CappedChain Deciding

def SourcePrefixFreshAccepted (key : ProgrammedGlobalChainKeygenView)
    (result : Forgery × SourceExactTracedState) : Prop :=
  ¬ SigningTranscript.ContainsRequest result.2.2.toSigningLog result.1 ∧
    ∃ encoding, TargetSum.decodeDigest (CacheView.encodingHash result.2.1.1.1 key.secretKey.parameter
      result.1.epoch (result.1.message, result.1.signature.randomness)) = some encoding

theorem sourcePrefix_freshAccepted_probability_le (adversary : XmssSecurity.TargetSum.Adversary)
    (key : ProgrammedGlobalChainKeygenView)
    (hkey : key ∈ support trajectoryProgrammedGlobalChainKeygen)
    (D : ℕ) (hD : Direct.IsDirectQueryBound adversary D) :
    Pr[SourcePrefixFreshAccepted key | sourcePrefixExecution adversary key] ≤
      TargetSum.acceptanceProbability * (D : ℝ≥0∞) := by
  have hbound := probEvent_freshAccepted_le_direct_budget key.publicKey
    (materializePrecomputation key.cache key.secretKey) (adversary.main key.publicKey) key.cache
    (keygen_cache_none_encodingInput key.keyResult
      (trajectoryProgrammedGlobalChainKeygen_support_keyResult key hkey)) D (hD key.publicKey)
  rw [← cappedBothTracedMappedAdversaryImpl_actionProjection key.publicKey
    (materializePrecomputation key.cache key.secretKey)
    (adversary.main key.publicKey) ((key.cache, []), []) [], probEvent_map] at hbound
  apply le_trans _ hbound
  apply probEvent_mono''
  rintro result ⟨hfresh, encoding, hdecode⟩
  exact hasFreshAcceptedEncoding_of_decode key.secretKey.parameter
    (result.2.1.1.1, result.2.2) result.1 encoding hfresh hdecode

/-- info: 'XmssSecurity.TargetSum.EUFCMA.sourcePrefix_freshAccepted_probability_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sourcePrefix_freshAccepted_probability_le

end XmssSecurity.TargetSum.EUFCMA
