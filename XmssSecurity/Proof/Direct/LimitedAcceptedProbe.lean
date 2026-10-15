import XmssSecurity.Proof.Direct.LimitedPrefixCoupling
import XmssSecurity.Proof.Direct.LimitedPrefixSupport

/-! A successful limited prefix incurs the deciding probe only when its forged encoding
is accepted. Aborted prefixes retain any collision already recorded in their trace. -/

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.Deciding

open CappedChain FirstLaneOracleSimulation

abbrev LimitedPrefixResult := Option (Forgery × GlobalHighDirectTracedState) × EncodingBudgetCounters

noncomputable def limitedAcceptedPrefixProbeExecution (limit : Nat) (key : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (computation : OracleComp (OracleWorld + SigningSpec) Forgery) :
    OracleComp GlobalFirstLaneWorld LimitedPrefixResult := do
  let result ← limitedFirstLanePrefix limit key edgeHigh computation
    (GlobalHighDirectTracedState.initial (globalFilteredCausalKeygenState key)) ⟨0, 0, 0⟩
  match result.1 with
  | none => pure result
  | some completed =>
      if (forgedEncoding completed.2.causalState.cache key.secretKey.parameter completed.1).isSome then
        let _ ← publicDecidingProbe completed.1.epoch
          (signedEncoding completed.2.causalState.cache key.secretKey.parameter
            completed.2.attackerTrace.toSigningLog completed.1.epoch)
          (prefixProbeEncoding completed.2.causalState.cache key.secretKey.parameter completed.1)
          completed.1.signature.chainValue
        pure result
      else pure result

noncomputable def appendLimitedAcceptedPrefixProbe (base : GlobalChainValueIndex → Digest)
    (key : ProgrammedGlobalChainKeygenView)
    (result : LimitedPrefixResult × ActionTrace GlobalChainValueIndex) :
    LimitedPrefixResult × ActionTrace GlobalChainValueIndex :=
  match result.1.1 with
  | none => result
  | some completed =>
      if (forgedEncoding completed.2.causalState.cache key.secretKey.parameter completed.1).isSome then
        (result.1, result.2 ++ (prefixProbeResult base completed.2.causalState.cache key.secretKey.parameter
          completed.2.attackerTrace.toSigningLog completed.1).2)
      else result

theorem limitedAcceptedPrefixProbeExecution_eager (limit : Nat) (key : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest) (edgeHigh : GlobalChainEdgeIndex → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) Forgery) :
    (simulateQ (eagerTraceImpl base) (limitedAcceptedPrefixProbeExecution limit key edgeHigh computation)).run =
      appendLimitedAcceptedPrefixProbe base key <$>
        (simulateQ (eagerTraceImpl base) (limitedFirstLanePrefix limit key edgeHigh computation
          (GlobalHighDirectTracedState.initial (globalFilteredCausalKeygenState key)) ⟨0, 0, 0⟩)).run := by
  unfold limitedAcceptedPrefixProbeExecution
  simp only [simulateQ_bind, WriterT.run_bind', map_eq_bind_pure_comp]
  apply bind_congr
  rintro ⟨⟨completed, counters⟩, trace⟩
  cases completed with
  | none => simp [appendLimitedAcceptedPrefixProbe, Prod.map]
  | some completed =>
      by_cases haccepted : (forgedEncoding completed.2.causalState.cache key.secretKey.parameter completed.1).isSome
      · simp only [haccepted, if_true, simulateQ_bind, WriterT.run_bind', publicDecidingProbe_eager,
          pure_bind, simulateQ_pure, WriterT.run_pure, map_pure]
        simp [appendLimitedAcceptedPrefixProbe, haccepted, prefixProbeResult, Prod.map]
      · simp [haccepted, appendLimitedAcceptedPrefixProbe, Prod.map]

theorem appendLimitedAcceptedPrefixProbe_preserves_hit (base : GlobalChainValueIndex → Digest)
    (key : ProgrammedGlobalChainKeygenView) (result : LimitedPrefixResult × ActionTrace GlobalChainValueIndex)
    (hhit : CombinedHit base result.2) :
    CombinedHit base (appendLimitedAcceptedPrefixProbe base key result).2 := by
  unfold appendLimitedAcceptedPrefixProbe
  split
  · exact hhit
  · split
    · exact CombinedHit.append_of_prefix base _ _ hhit
    · exact hhit

def LimitedPrefixForgedEncodingAccepted (key : ProgrammedGlobalChainKeygenView)
    (result : LimitedPrefixResult × ActionTrace GlobalChainValueIndex) : Prop :=
  ∃ completed, result.1.1 = some completed ∧
    (forgedEncoding completed.2.causalState.cache key.secretKey.parameter completed.1).isSome

noncomputable instance (key : ProgrammedGlobalChainKeygenView) :
    DecidablePred (LimitedPrefixForgedEncodingAccepted key) := Classical.decPred _

theorem hazardCount_appendLimitedAcceptedPrefixProbe (base : GlobalChainValueIndex → Digest)
    (key : ProgrammedGlobalChainKeygenView) (result : LimitedPrefixResult × ActionTrace GlobalChainValueIndex) :
    hazardCount (appendLimitedAcceptedPrefixProbe base key result).2 = hazardCount result.2 +
      if LimitedPrefixForgedEncodingAccepted key result then 1 else 0 := by
  classical
  rcases result with ⟨⟨completed, counters⟩, trace⟩
  cases completed with
  | none => simp [appendLimitedAcceptedPrefixProbe, LimitedPrefixForgedEncodingAccepted]
  | some completed =>
      by_cases h : (forgedEncoding completed.2.causalState.cache key.secretKey.parameter completed.1).isSome
      all_goals simp [appendLimitedAcceptedPrefixProbe, LimitedPrefixForgedEncodingAccepted, h,
        hazardCount_append, prefixProbeResult, decidingProbeResult_hazardCount]

theorem limitedPrefixForgedEncodingAccepted_probability_le_expected
    (table : GlobalChainValueIndex → Digest) (limit : Nat) (key : ProgrammedGlobalChainKeygenView)
    (hkey : key ∈ support trajectoryProgrammedGlobalChainKeygen)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (computation : OracleComp (OracleWorld + SigningSpec) Forgery) :
    Pr[LimitedPrefixForgedEncodingAccepted key |
      (simulateQ (eagerTraceImpl table) (limitedFirstLanePrefix limit key edgeHigh computation
        (GlobalHighDirectTracedState.initial (globalFilteredCausalKeygenState key)) ⟨0, 0, 0⟩)).run] ≤
      TargetSum.acceptanceProbability * expectedSimulatedQueryCount (eagerUnitImpl table) IsEncodingSample
        (limitedFirstLanePrefix limit key edgeHigh computation
          (GlobalHighDirectTracedState.initial (globalFilteredCausalKeygenState key)) ⟨0, 0, 0⟩) () := by
  apply le_trans _ (limitedFirstLanePrefix_accepted_probability_le_expected table limit key hkey edgeHigh computation _)
  apply probEvent_mono
  intro result _hresult haccepted
  obtain ⟨completed, hcompleted, haccepted⟩ := haccepted
  refine ⟨completed, hcompleted, ?_⟩
  cases hdecode : forgedEncoding completed.2.causalState.cache key.secretKey.parameter completed.1 with
  | none => simp [hdecode] at haccepted
  | some encoding => exact hasAcceptedEncoding_of_decode _ _ _ _ _ _ hdecode

theorem expected_limitedAcceptedPrefixProbe_hazards
    (table : GlobalChainValueIndex → Digest) (limit : Nat) (key : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (computation : OracleComp (OracleWorld + SigningSpec) Forgery) :
    expectedSimulatedQueryCount (eagerUnitImpl table) IsHazardQuery
      (limitedAcceptedPrefixProbeExecution limit key edgeHigh computation) () =
      expectedSimulatedQueryCount (eagerUnitImpl table) IsHazardQuery
        (limitedFirstLanePrefix limit key edgeHigh computation
          (GlobalHighDirectTracedState.initial (globalFilteredCausalKeygenState key)) ⟨0, 0, 0⟩) () +
      Pr[LimitedPrefixForgedEncodingAccepted key |
        (simulateQ (eagerTraceImpl table) (limitedFirstLanePrefix limit key edgeHigh computation
          (GlobalHighDirectTracedState.initial (globalFilteredCausalKeygenState key)) ⟨0, 0, 0⟩)).run] := by
  classical
  rw [expectedHazardQueries_eq_trace, limitedAcceptedPrefixProbeExecution_eager, tsum_probOutput_map_mul,
    expectedHazardQueries_eq_trace]
  simp_rw [hazardCount_appendLimitedAcceptedPrefixProbe, Nat.cast_add, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero, mul_add]
  rw [ENNReal.tsum_add]
  congr 1
  rw [probEvent_eq_tsum_ite]
  apply tsum_congr
  intro result
  split_ifs <;> simp

theorem expected_limitedAcceptedPrefixProbe_hazards_le
    (table : GlobalChainValueIndex → Digest) (limit : Nat) (key : ProgrammedGlobalChainKeygenView)
    (hkey : key ∈ support trajectoryProgrammedGlobalChainKeygen)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (computation : OracleComp (OracleWorld + SigningSpec) Forgery) :
    expectedSimulatedQueryCount (eagerUnitImpl table) IsHazardQuery
      (limitedAcceptedPrefixProbeExecution limit key edgeHigh computation) () ≤
      expectedSimulatedQueryCount (eagerUnitImpl table) IsHazardQuery
        (limitedFirstLanePrefix limit key edgeHigh computation
          (GlobalHighDirectTracedState.initial (globalFilteredCausalKeygenState key)) ⟨0, 0, 0⟩) () +
      TargetSum.acceptanceProbability * expectedSimulatedQueryCount (eagerUnitImpl table) IsEncodingSample
        (limitedFirstLanePrefix limit key edgeHigh computation
          (GlobalHighDirectTracedState.initial (globalFilteredCausalKeygenState key)) ⟨0, 0, 0⟩) () := by
  rw [expected_limitedAcceptedPrefixProbe_hazards]
  exact add_le_add le_rfl
    (limitedPrefixForgedEncodingAccepted_probability_le_expected table limit key hkey edgeHigh computation)

theorem limitedAcceptedPrefixProbe_trace_bound
    (table : GlobalChainValueIndex → Digest) (limit : Nat) (key : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (computation : OracleComp (OracleWorld + SigningSpec) Forgery)
    (result : LimitedPrefixResult × ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support (simulateQ (eagerTraceImpl table)
      (limitedAcceptedPrefixProbeExecution limit key edgeHigh computation)).run) :
    hazardCount result.2 ≤ limit + 1 := by
  rw [limitedAcceptedPrefixProbeExecution_eager, support_map] at hresult
  obtain ⟨prefixResult, hprefix, rfl⟩ := hresult
  have hbudget := limitedFirstLanePrefix_trace_budget table limit key edgeHigh computation
    (GlobalHighDirectTracedState.initial (globalFilteredCausalKeygenState key)) ⟨0, 0, 0⟩
    (by simp [EncodingBudgetCounters.charge]) prefixResult hprefix
  have hcount := limitedFirstLanePrefix_trace_direct table limit key edgeHigh computation
    (GlobalHighDirectTracedState.initial (globalFilteredCausalKeygenState key)) ⟨0, 0, 0⟩ prefixResult hprefix
  have hdirect : prefixResult.1.2.direct ≤ limit :=
    (Nat.le_add_right _ _).trans hbudget.1
  rw [hazardCount_appendLimitedAcceptedPrefixProbe]
  split_ifs <;> omega

theorem limitedAcceptedPrefixEvent_coupling
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView × (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support trajectoryProgrammedGlobalChainKeygen)
    (limit : Nat) (computation : OracleComp (OracleWorld + SigningSpec) Forgery)
    (hbudget : CountedSourceBudget (Concrete.materializePrecomputation left.cache left.secretKey)
      limit computation (CountedSourceState.initial left.cache)) :
    RelTriple
      ((simulateQ (countedSourceImpl (Concrete.materializePrecomputation left.cache left.secretKey))
        computation).run (CountedSourceState.initial left.cache))
      ((simulateQ (eagerTraceImpl right.1.2)
        (limitedAcceptedPrefixProbeExecution limit right.1.1 right.2 computation)).run)
      (fun source target => AcceptedPrefixFirstLaneEvent left (source.1, source.2.toSource) →
        CombinedHit right.1.2 target.2) := by
  rw [limitedAcceptedPrefixProbeExecution_eager, ← id_map
    ((simulateQ (countedSourceImpl (Concrete.materializePrecomputation left.cache left.secretKey))
      computation).run (CountedSourceState.initial left.cache))]
  apply relTriple_map
  apply relTriple_post_mono (relTriple_with_support
    (relTriple_countedSource_limitedPrefix left right hrel hleftSupport hrightSupport limit computation hbudget))
  intro source target hresult hevent
  obtain ⟨⟨_hsourceBudget, _htargetBudget, _hsamples, _hhazards, hrelation⟩, _hsource, htarget⟩ := hresult
  rcases hrelation with ⟨state, hvalue, hgood, _hcounters, _hcount⟩ | hhit
  · simp only [List.nil_append] at hgood
    have hparameter := programmedGlobal_secretKey_parameter_eq left right hrel hleftSupport hrightSupport
    obtain ⟨_monitor, _hmonitor, _hagrees, _hrevealed, hcausal, _hretained⟩ := hgood.1.1
    have hencoding : forgedEncoding source.2.counts.cache left.secretKey.parameter source.1 =
        forgedEncoding state.causalState.cache right.1.1.secretKey.parameter source.1 := by
      rw [hparameter]
      exact forgedEncoding_eq_of_comparableCaches _ _ _ hcausal.1 _
    have haccepted : (forgedEncoding state.causalState.cache right.1.1.secretKey.parameter source.1).isSome := by
      rw [← hencoding]
      exact hevent.2
    have hcovered := limitedFirstLanePrefix_returnedCovered right.1.2 limit right.1.1 right.2
      computation ⟨0, 0, 0⟩ target (source.1, state) htarget hvalue
    change CombinedHit right.1.2 (appendLimitedAcceptedPrefixProbe right.1.2 right.1.1 target).2
    simp only [appendLimitedAcceptedPrefixProbe, hvalue, if_pos haccepted]
    exact prefixFirstLaneEvent_good_implies_hit left right hrel hleftSupport hrightSupport
      (source.1, source.2.toSource) ((source.1, state), target.2) rfl hgood hcovered hevent.1
  · exact appendLimitedAcceptedPrefixProbe_preserves_hit right.1.2 right.1.1 target
      (by simpa only [List.nil_append] using hhit)

/-- info: 'XmssSecurity.Deciding.limitedAcceptedPrefixEvent_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms limitedAcceptedPrefixEvent_coupling

/-- info: 'XmssSecurity.Deciding.expected_limitedAcceptedPrefixProbe_hazards' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms expected_limitedAcceptedPrefixProbe_hazards

end XmssSecurity.Deciding
