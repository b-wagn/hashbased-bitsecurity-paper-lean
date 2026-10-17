import XmssSecurity.Proof.TargetSum.Modes.SignerClassBudget
import XmssSecurity.Proof.TargetSum.Direct.SourceLossBudget
import XmssSecurity.Proof.TargetSum.Modes.SignerLimitedCoupling

/-! Adversaries whose forged encoding is already cached when they output the forgery. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Direct

def HasCachedForgedEncoding (adversary : Adversary) : Prop :=
  ∀ keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅),
    ∀ result ∈ support ((simulateQ romImpl
      (Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run keyResult.2),
      result.2 (Concrete.CacheView.encodingInput keyResult.1.2.parameter result.1.1.epoch
        (result.1.1.message, result.1.1.signature.randomness)) ≠ none

theorem HasCachedForgedEncoding.sourcePrefix {adversary : Adversary}
    (hcached : HasCachedForgedEncoding adversary)
    (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (hkey : key ∈ support CappedChain.trajectoryProgrammedGlobalChainKeygen)
    (result : Forgery × CappedChain.SourceExactTracedState)
    (hresult : result ∈ support (Deciding.sourcePrefixExecution adversary key)) :
    result.2.1.1.1 (Concrete.CacheView.encodingInput key.secretKey.parameter result.1.epoch
      (result.1.message, result.1.signature.randomness)) ≠ none := by
  have hmaterialized : Concrete.materializeCachedKeyResult key.keyResult ∈ support
      ((simulateQ romImpl Concrete.scheme.keygen).run ∅) := by
    apply (mem_support_iff_of_evalDist_eq
      CappedChain.evalDist_materializedTrajectoryGlobalChainKeygen_eq_cappedKeygen _).mp
    rw [support_map]
    exact ⟨key, hkey, rfl⟩
  exact hcached (Concrete.materializeCachedKeyResult key.keyResult) hmaterialized
    ((result.1, result.2.2.toSigningLog), result.2.1.1.1)
    (Deciding.sourcePrefixExecution_phase_support adversary key result hresult)

end XmssSecurity.TargetSum.Direct
