import Xmss.Proof.TargetSum.Direct.SourceBudgetExhaustion
import Xmss.Proof.TargetSum.Direct.MixedFirstLane
import Xmss.Proof.TargetSum.Direct.SourceSigningCost
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! The public first-lane state can recognize a rejecting last nonencoding query.
On related executions this terminal cut excludes only cached first-lane witnesses. -/

open OracleComp OracleSpec ENNReal
open scoped Classical

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum.CappedExecution

open Xmss.TargetSum.Keygen Xmss.TargetSum.Signing
open Hashing Wots Merkle Verify Keygen Signing
open Deciding Seeded FirstLaneOracleSimulation

theorem hasAcceptedEncoding_iff_of_comparableCaches (parameter : PublicParameter)
    (left right : QueryCache HashSpec)
    (hagrees : HashCachesAgreeOn (CappedExecution.GlobalSigningComparableHashInput parameter) left right) :
    HasAcceptedEncoding parameter left ↔ HasAcceptedEncoding parameter right := by
  have hencoding (input : HashInput) (hinput : (encodingInputLeafIndex? parameter input).isSome) :
      left input = right input := by
    obtain ⟨leaf, hleaf⟩ := Option.isSome_iff_exists.mp hinput
    obtain ⟨⟨message, randomness⟩, hinput⟩ :=
      exists_encodingInput_of_encodingInputLeafIndex?_eq_some parameter input leaf hleaf
    exact hagrees input ⟨leaf, message, randomness, hinput.symm⟩
  constructor
  · rintro ⟨input, output, houtput, hinput, hvalid⟩
    exact ⟨input, output, (hencoding input hinput).symm.trans houtput, hinput, hvalid⟩
  · rintro ⟨input, output, houtput, hinput, hvalid⟩
    exact ⟨input, output, (hencoding input hinput).trans houtput, hinput, hvalid⟩

theorem firstLaneCounters_charge_le_source_of_related
    (left : CappedExecution.ProgrammedGlobalChainKeygenView) (right : Deciding.BaseKey)
    (hrel : CappedExecution.ProgrammedGlobalChainKeygenBaseStableRelation left right)
    (hleft : left ∈ support CappedExecution.trajectoryProgrammedGlobalChainKeygen)
    (hright : right.1 ∈ support CappedExecution.trajectoryProgrammedGlobalChainKeygen)
    (source : CountedSourceState) (target : CappedExecution.GlobalDirectTracedState)
    (history : FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex)
    (hstate : CappedExecution.SourceFirstLaneExactGoodStateRelation left right source.toSource target history)
    (hcacheCount : cachedEncodingInputCount target.causalState.cache right.1.secretKey.parameter =
      (history.encodingActions.length : ℝ≥0∞))
    (hencoding : CountedSourceEncodingBudget left.secretKey.parameter source)
    (hsourceTrace : source.counts.direct = source.attackerTrace.hashInputs.length) :
    (firstLaneCounters right.1.secretKey.parameter target history).charge ≤ source.charge := by
  have hparameter := CappedExecution.programmedGlobal_secretKey_parameter_eq left right hrel hleft hright
  have htrace : source.attackerTrace = target.attackerTrace := hstate.1.2
  obtain ⟨_monitor, _hmonitor, _hagrees, _hrevealed, hcausal, _hretained⟩ := hstate.1.1
  change CappedExecution.GlobalFilteredCausalStateRelation left right source.counts.cache target.causalState at hcausal
  have hcacheEq := encodingInputCount_eq_of_globalSigning_agree left.secretKey.parameter
    source.counts.cache target.causalState.cache hcausal.1
  change cachedEncodingInputCount source.counts.cache left.secretKey.parameter ≤
    ((source.attackerTrace.encodingInputCount left.secretKey.parameter + source.counts.signing : Nat) : ℝ≥0∞)
    at hencoding
  rw [hcacheEq, ← hparameter, hcacheCount] at hencoding
  have hsamples : history.encodingActions.length ≤
      source.attackerTrace.encodingInputCount right.1.secretKey.parameter + source.counts.signing :=
    by exact_mod_cast hencoding
  unfold firstLaneCounters EncodingBudgetCounters.charge CountedSourceState.charge
  rw [← htrace, ← hsourceTrace]
  dsimp only
  omega

noncomputable def RejectingLastNonencoding (limit : Nat) (key : CappedExecution.ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain) (state : CappedExecution.GlobalDirectTracedState)
    (counters : EncodingBudgetCounters) : Prop :=
  limit ≤ counters.charge + 1 ∧ ¬HasAcceptedEncoding key.secretKey.parameter state.causalState.cache ∧
    ∃ hashInput, input = .inl (.inr hashInput) ∧
      ¬CappedEncodingMonitor.IsEncodingHashQuery key.secretKey.parameter (.inr hashInput)

theorem rejectingLastNonencoding_source_noAccepted {α : Type}
    (left : CappedExecution.ProgrammedGlobalChainKeygenView) (right : Deciding.BaseKey)
    (hrel : CappedExecution.ProgrammedGlobalChainKeygenBaseStableRelation left right)
    (hleft : left ∈ support CappedExecution.trajectoryProgrammedGlobalChainKeygen)
    (hright : right.1 ∈ support CappedExecution.trajectoryProgrammedGlobalChainKeygen)
    (limit : Nat) (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (source : CountedSourceState) (target : CappedExecution.GlobalDirectTracedState)
    (history : FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex)
    (hstate : CappedExecution.SourceFirstLaneExactGoodStateRelation left right source.toSource target history)
    (hcacheCount : cachedEncodingInputCount target.causalState.cache right.1.secretKey.parameter =
      (history.encodingActions.length : ℝ≥0∞))
    (hencoding : CountedSourceEncodingBudget left.secretKey.parameter source)
    (hsourceTrace : source.counts.direct = source.attackerTrace.hashInputs.length)
    (hbudget : CountedSourceBudget (Keygen.materializePrecomputation left.cache left.secretKey) limit
      (liftM ((OracleWorld + SigningSpec).query input) >>= next) source)
    (hcut : RejectingLastNonencoding limit right.1 input target
      (firstLaneCounters right.1.secretKey.parameter target history))
    (result : α × CountedSourceState)
    (hresult : result ∈ support ((simulateQ (countedSourceImpl (Keygen.materializePrecomputation left.cache left.secretKey))
      (liftM ((OracleWorld + SigningSpec).query input) >>= next)).run source)) :
    ¬HasAcceptedEncoding left.secretKey.parameter result.2.counts.cache := by
  have hcharge := firstLaneCounters_charge_le_source_of_related left right hrel hleft hright
    source target history hstate hcacheCount hencoding hsourceTrace
  have hparameter := CappedExecution.programmedGlobal_secretKey_parameter_eq left right hrel hleft hright
  obtain ⟨hlast, hrejecting, hashInput, rfl, hinput⟩ := hcut
  obtain ⟨_monitor, _hmonitor, _hagrees, _hrevealed, hcausal, _hretained⟩ := hstate.1.1
  change CappedExecution.GlobalFilteredCausalStateRelation left right source.counts.cache target.causalState at hcausal
  have hcache : ¬HasAcceptedEncoding left.secretKey.parameter source.counts.cache := by
    rw [hasAcceptedEncoding_iff_of_comparableCaches _ _ _ hcausal.1]
    simpa only [hparameter] using hrejecting
  rw [← Keygen.materializePrecomputation_parameter left.cache left.secretKey]
  apply hbudget.noAcceptedEncoding_after_last_nonencoding (by omega)
    (by rw [Keygen.materializePrecomputation_parameter]; exact hcache) _ result hresult
  rw [Keygen.materializePrecomputation_parameter]
  rw [← hparameter]
  exact hinput

noncomputable def TerminalPrefixCut (limit : Nat) (key : CappedExecution.ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain) (state : CappedExecution.GlobalDirectTracedState)
    (counters : EncodingBudgetCounters) : Prop :=
  RejectingLastNonencoding limit key input state counters ∨
    (limit ≤ counters.charge + 1 ∧ ∃ request, input = .inr request) ∨
    (limit ≤ counters.charge ∧ ∃ hashInput, input = .inl (.inr hashInput))

theorem terminalPrefixCut_source_noAccepted {α : Type}
    (left : CappedExecution.ProgrammedGlobalChainKeygenView) (right : Deciding.BaseKey)
    (hrel : CappedExecution.ProgrammedGlobalChainKeygenBaseStableRelation left right)
    (hleft : left ∈ support CappedExecution.trajectoryProgrammedGlobalChainKeygen)
    (hright : right.1 ∈ support CappedExecution.trajectoryProgrammedGlobalChainKeygen)
    (limit : Nat) (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (source : CountedSourceState) (target : CappedExecution.GlobalDirectTracedState)
    (history : FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex)
    (hstate : CappedExecution.SourceFirstLaneExactGoodStateRelation left right source.toSource target history)
    (hcacheCount : cachedEncodingInputCount target.causalState.cache right.1.secretKey.parameter =
      (history.encodingActions.length : ℝ≥0∞))
    (hencoding : CountedSourceEncodingBudget left.secretKey.parameter source)
    (hsourceTrace : source.counts.direct = source.attackerTrace.hashInputs.length)
    (hbudget : CountedSourceBudget (Keygen.materializePrecomputation left.cache left.secretKey) limit
      (liftM ((OracleWorld + SigningSpec).query input) >>= next) source)
    (hcut : TerminalPrefixCut limit right.1 input target
      (firstLaneCounters right.1.secretKey.parameter target history))
    (result : α × CountedSourceState)
    (hresult : result ∈ support ((simulateQ (countedSourceImpl (Keygen.materializePrecomputation left.cache left.secretKey))
      (liftM ((OracleWorld + SigningSpec).query input) >>= next)).run source)) :
    ¬HasAcceptedEncoding left.secretKey.parameter result.2.counts.cache := by
  have hcharge := firstLaneCounters_charge_le_source_of_related left right hrel hleft hright
    source target history hstate hcacheCount hencoding hsourceTrace
  rcases hcut with hrejecting | ⟨hlast, request, rfl⟩ | ⟨hexhausted, hashInput, rfl⟩
  · exact rejectingLastNonencoding_source_noAccepted left right hrel hleft hright limit input next
      source target history hstate hcacheCount hencoding hsourceTrace hbudget hrejecting result hresult
  · have hroom := hbudget.signing_room
    omega
  · have hroom := hbudget.direct_hash_room
    omega

/-- info: 'Xmss.TargetSum.CappedExecution.rejectingLastNonencoding_source_noAccepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rejectingLastNonencoding_source_noAccepted

/-- info: 'Xmss.TargetSum.CappedExecution.terminalPrefixCut_source_noAccepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms terminalPrefixCut_source_noAccepted

end Xmss.TargetSum.CappedExecution
