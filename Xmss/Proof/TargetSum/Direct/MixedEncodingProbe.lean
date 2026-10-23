import Xmss.Proof.TargetSum.Direct.LimitedEncodingProbe
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! A single prefix experiment chooses its cached forged encoding when accepted,
or an independently supplied fallback encoding. Both branches share the prefix trace. -/

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational
open scoped Classical

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum.Deciding

open CappedExecution FirstLaneOracleSimulation

noncomputable def mixedProbeEncoding (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (forgery : Forgery) (fallback : Option Encoding) : Option Encoding :=
  (Deciding.forgedEncoding cache parameter forgery).orElse (fun _ => fallback)

def MixedEncodingPrefixEvent (key : CappedExecution.ProgrammedGlobalChainKeygenView)
    (result : Forgery × CappedExecution.SourceExactTracedState) (fallback : Option Encoding) : Prop :=
  AcceptedPrefixFirstLaneEvent key result ∨
    (Deciding.forgedEncoding result.2.1.1.1 key.secretKey.parameter result.1 = none ∧
      ∃ encoding, fallback = some encoding ∧ RevealedEncodingPrefixEvent key result encoding)

noncomputable def limitedMixedEncodingProbeExecution (limit : Nat) (key : CappedExecution.ProgrammedGlobalChainKeygenView)
    (computation : OracleComp (OracleWorld + SigningSpec) Forgery)
    (fallback : Option Encoding) : OracleComp CappedExecution.GlobalFirstLaneWorld LimitedPrefixResult := do
  let result ← limitedFirstLanePrefix limit key computation
    (CappedExecution.GlobalDirectTracedState.initial (CappedExecution.globalFilteredCausalKeygenState key)) ⟨0, 0, 0⟩
  match result.1 with
  | none => pure result
  | some completed =>
      match mixedProbeEncoding completed.2.causalState.cache key.secretKey.parameter completed.1 fallback with
      | none => pure result
      | some encoding =>
          let _ ← Deciding.publicDecidingProbe completed.1.epoch
            (Deciding.signedEncoding completed.2.causalState.cache key.secretKey.parameter
              completed.2.attackerTrace.toSigningLog completed.1.epoch)
            encoding completed.1.signature.chainValue
          pure result

noncomputable def appendLimitedMixedEncodingProbe (base : CappedExecution.GlobalChainValueIndex → Digest)
    (key : CappedExecution.ProgrammedGlobalChainKeygenView) (fallback : Option Encoding)
    (result : LimitedPrefixResult × FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex) :
    LimitedPrefixResult × FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex :=
  match result.1.1 with
  | none => result
  | some completed =>
      match mixedProbeEncoding completed.2.causalState.cache key.secretKey.parameter completed.1 fallback with
      | none => result
      | some encoding => appendLimitedEncodingPrefixProbe base key encoding result

def LimitedMixedEncodingProbeEligible (key : CappedExecution.ProgrammedGlobalChainKeygenView) (fallback : Option Encoding)
    (result : LimitedPrefixResult × FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex) : Prop :=
  ∃ completed, result.1.1 = some completed ∧
    (mixedProbeEncoding completed.2.causalState.cache key.secretKey.parameter completed.1 fallback).isSome

theorem limitedMixedEncodingProbeExecution_eager (limit : Nat) (key : CappedExecution.ProgrammedGlobalChainKeygenView)
    (base : CappedExecution.GlobalChainValueIndex → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) Forgery) (fallback : Option Encoding) :
    (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl base) (limitedMixedEncodingProbeExecution limit key computation fallback)).run =
      appendLimitedMixedEncodingProbe base key fallback <$>
        (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl base) (limitedFirstLanePrefix limit key computation
          (CappedExecution.GlobalDirectTracedState.initial (CappedExecution.globalFilteredCausalKeygenState key)) ⟨0, 0, 0⟩)).run := by
  unfold limitedMixedEncodingProbeExecution
  simp only [simulateQ_bind, WriterT.run_bind', map_eq_bind_pure_comp]
  apply bind_congr
  rintro ⟨⟨completed, counters⟩, trace⟩
  cases completed with
  | none => simp [appendLimitedMixedEncodingProbe, Prod.map]
  | some completed =>
      cases hencoding : mixedProbeEncoding completed.2.causalState.cache key.secretKey.parameter completed.1 fallback with
      | none => simp [hencoding, appendLimitedMixedEncodingProbe, Prod.map]
      | some encoding =>
          simp only [hencoding, simulateQ_bind, WriterT.run_bind', Deciding.publicDecidingProbe_eager,
            pure_bind, simulateQ_pure, WriterT.run_pure, map_pure]
          simp [appendLimitedMixedEncodingProbe, hencoding, appendLimitedEncodingPrefixProbe, Prod.map]

theorem appendLimitedMixedEncodingProbe_preserves_hit (base : CappedExecution.GlobalChainValueIndex → Digest)
    (key : CappedExecution.ProgrammedGlobalChainKeygenView) (fallback : Option Encoding)
    (result : LimitedPrefixResult × FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex)
    (hhit : FirstLaneOracleSimulation.CombinedHit base result.2) :
    FirstLaneOracleSimulation.CombinedHit base (appendLimitedMixedEncodingProbe base key fallback result).2 := by
  unfold appendLimitedMixedEncodingProbe
  split
  · exact hhit
  · split
    · exact hhit
    · exact appendLimitedEncodingPrefixProbe_preserves_hit _ _ _ _ hhit

theorem hazardCount_appendLimitedMixedEncodingProbe (base : CappedExecution.GlobalChainValueIndex → Digest)
    (key : CappedExecution.ProgrammedGlobalChainKeygenView) (fallback : Option Encoding)
    (result : LimitedPrefixResult × FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex) :
    FirstLaneOracleSimulation.hazardCount (appendLimitedMixedEncodingProbe base key fallback result).2 = FirstLaneOracleSimulation.hazardCount result.2 +
      if LimitedMixedEncodingProbeEligible key fallback result then 1 else 0 := by
  rcases result with ⟨⟨completed, counters⟩, trace⟩
  cases completed with
  | none => simp [appendLimitedMixedEncodingProbe, LimitedMixedEncodingProbeEligible]
  | some completed =>
      cases hencoding : mixedProbeEncoding completed.2.causalState.cache key.secretKey.parameter completed.1 fallback with
      | none => simp [appendLimitedMixedEncodingProbe, LimitedMixedEncodingProbeEligible, hencoding]
      | some encoding =>
          simp [appendLimitedMixedEncodingProbe, LimitedMixedEncodingProbeEligible, hencoding,
            appendLimitedEncodingPrefixProbe, FirstLaneOracleSimulation.hazardCount_append, Deciding.decidingProbeResult_hazardCount]

theorem mixedEncodingPrefixEvent_implies_accepted (key : CappedExecution.ProgrammedGlobalChainKeygenView)
    (result : Forgery × CountedSourceState) (fallback : Option Encoding)
    (hevent : MixedEncodingPrefixEvent key (result.1, result.2.toSource) fallback) :
    HasAcceptedEncoding key.secretKey.parameter result.2.counts.cache ∨ fallback.isSome := by
  rcases hevent with hcached | ⟨_, encoding, hencoding, _⟩
  · exact Or.inl (acceptedPrefixFirstLane_implies_accepted key result hcached)
  · exact Or.inr (by simp [hencoding])

theorem limitedMixedEncoding_cancellation_coupling_afterKeygen (adversary : Adversary) (limit : Nat)
    (left : CappedExecution.ProgrammedGlobalChainKeygenView) (right : Deciding.BaseKey)
    (hrel : CappedExecution.ProgrammedGlobalChainKeygenBaseStableRelation left right)
    (hleft : left ∈ support CappedExecution.trajectoryProgrammedGlobalChainKeygen)
    (hright : right.1 ∈ support CappedExecution.trajectoryProgrammedGlobalChainKeygen)
    (hbudget : CountedSourceBudget (Keygen.materializePrecomputation left.cache left.secretKey)
      limit (adversary.main left.publicKey) (CountedSourceState.initial left.cache)) (fallback : Option Encoding) :
    RelTriple (sourceCountedPrefixExecution adversary left)
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.2)
        (publicLimitedPrefixExecution limit adversary right.1)).run)
      (fun source target =>
        (MixedEncodingPrefixEvent left (source.1, source.2.toSource) fallback →
          (HasAcceptedEncoding left.secretKey.parameter source.2.counts.cache ∨ fallback.isSome) ∧
            FirstLaneOracleSimulation.CombinedHit right.2 (appendLimitedMixedEncodingProbe right.2 right.1 fallback target).2) ∧
        (LimitedMixedEncodingProbeEligible right.1 fallback target →
          (HasAcceptedEncoding left.secretKey.parameter source.2.counts.cache ∨ fallback.isSome) ∨
            FirstLaneOracleSimulation.CombinedHit right.2 (appendLimitedMixedEncodingProbe right.2 right.1 fallback target).2)) := by
  have hcoupling := relTriple_countedSource_limitedPrefix left right hrel hleft hright limit
    (adversary.main left.publicKey) hbudget
  have hpk : left.publicKey = right.1.publicKey := hrel.1.toStable.1.2.1
  change RelTriple (sourceCountedPrefixExecution adversary left)
    ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.2) (limitedFirstLanePrefix limit right.1
      (adversary.main left.publicKey)
      (CappedExecution.GlobalDirectTracedState.initial (CappedExecution.globalFilteredCausalKeygenState right.1)) ⟨0, 0, 0⟩)).run) _ at hcoupling
  rw [hpk] at hcoupling
  apply relTriple_post_mono (relTriple_with_support hcoupling)
  intro source target hresult
  rcases hresult.1.2.2.2.2 with ⟨state, hvalue, hgood, _hcounters, _hcount⟩ | hhit
  · simp only [List.nil_append] at hgood
    have hparameter := CappedExecution.programmedGlobal_secretKey_parameter_eq left right hrel hleft hright
    obtain ⟨_monitor, _hmonitor, _hagrees, _hrevealed, hcausal, _hretained⟩ := hgood.1.1
    have hencoding : Deciding.forgedEncoding source.2.counts.cache left.secretKey.parameter source.1 =
        Deciding.forgedEncoding state.causalState.cache right.1.secretKey.parameter source.1 := by
      rw [hparameter]
      exact forgedEncoding_eq_of_comparableCaches _ _ _ hcausal.1 _
    have hcovered := limitedFirstLanePrefix_returnedCovered right.2 limit right.1
      (adversary.main right.1.publicKey) ⟨0, 0, 0⟩ target (source.1, state) hresult.2.2 hvalue
    constructor
    · intro hevent
      refine ⟨mixedEncodingPrefixEvent_implies_accepted left source fallback hevent, ?_⟩
      rcases hevent with hcached | ⟨hnone, encoding, hfallback, hrevealed⟩
      · obtain ⟨encoding, hdecode⟩ := Option.isSome_iff_exists.mp hcached.2
        change Deciding.forgedEncoding source.2.counts.cache left.secretKey.parameter source.1 = some encoding at hdecode
        rw [hencoding] at hdecode
        simp only [appendLimitedMixedEncodingProbe, hvalue, mixedProbeEncoding, hdecode, Option.orElse_some]
        have hhit := Deciding.prefixFirstLaneEvent_good_implies_hit left right hrel hleft hright
          (source.1, source.2.toSource) ((source.1, state), target.2) rfl hgood hcovered hcached.1
        simpa only [appendLimitedEncodingPrefixProbe, hvalue, Deciding.prefixProbeResult, Deciding.prefixProbeEncoding,
          hdecode, Option.getD_some] using hhit
      · change Deciding.forgedEncoding source.2.counts.cache left.secretKey.parameter source.1 = none at hnone
        rw [hencoding] at hnone
        simp only [appendLimitedMixedEncodingProbe, hvalue, mixedProbeEncoding, hnone,
          Option.orElse_none, hfallback, appendLimitedEncodingPrefixProbe]
        exact revealedEncodingPrefixEvent_good_implies_hit left right hrel hleft hright
          (source.1, source.2.toSource) ((source.1, state), target.2) rfl hgood hcovered encoding hrevealed
    · rintro ⟨completed, hcompleted, heligible⟩
      rw [hvalue] at hcompleted
      cases hcompleted
      unfold mixedProbeEncoding at heligible
      rw [← hencoding] at heligible
      cases hdecode : Deciding.forgedEncoding source.2.counts.cache left.secretKey.parameter source.1 with
      | none => exact Or.inl (Or.inr (by simpa [hdecode] using heligible))
      | some encoding => exact Or.inl (Or.inl (hasAcceptedEncoding_of_decode _ _ _ _ _ _ hdecode))
  · have hprobed := appendLimitedMixedEncodingProbe_preserves_hit right.2 right.1 fallback target
      (by simpa only [List.nil_append] using hhit)
    exact ⟨fun hevent => ⟨mixedEncodingPrefixEvent_implies_accepted left source fallback hevent, hprobed⟩,
      fun _ => Or.inr hprobed⟩

/-- info: 'Xmss.TargetSum.Deciding.limitedMixedEncoding_cancellation_coupling_afterKeygen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms limitedMixedEncoding_cancellation_coupling_afterKeygen

end Xmss.TargetSum.Deciding
