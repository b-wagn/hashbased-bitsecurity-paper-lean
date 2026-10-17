import XmssSecurity.Proof.TargetSum.Direct.RevealedEncodingPrefix

/-! Append one deciding probe for an independently supplied encoding to the
limited adversary prefix. The complete public experiment uses at most q + 1 hazards. -/

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Deciding

open CappedChain FirstLaneOracleSimulation

noncomputable def limitedEncodingPrefixProbeExecution (limit : Nat) (key : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (computation : OracleComp (OracleWorld + SigningSpec) Forgery)
    (encoding : Encoding) : OracleComp GlobalFirstLaneWorld LimitedPrefixResult := do
  let result ← limitedFirstLanePrefix limit key edgeHigh computation
    (GlobalHighDirectTracedState.initial (globalFilteredCausalKeygenState key)) ⟨0, 0, 0⟩
  match result.1 with
  | none => pure result
  | some completed =>
      let _ ← publicDecidingProbe completed.1.epoch
        (signedEncoding completed.2.causalState.cache key.secretKey.parameter
          completed.2.attackerTrace.toSigningLog completed.1.epoch)
        encoding completed.1.signature.chainValue
      pure result

noncomputable def appendLimitedEncodingPrefixProbe (base : GlobalChainValueIndex → Digest)
    (key : ProgrammedGlobalChainKeygenView) (encoding : Encoding)
    (result : LimitedPrefixResult × ActionTrace GlobalChainValueIndex) :
    LimitedPrefixResult × ActionTrace GlobalChainValueIndex :=
  match result.1.1 with
  | none => result
  | some completed =>
      (result.1, result.2 ++ (decidingProbeResult base completed.1.epoch
        (signedEncoding completed.2.causalState.cache key.secretKey.parameter
          completed.2.attackerTrace.toSigningLog completed.1.epoch)
        encoding completed.1.signature.chainValue).2)

theorem limitedEncodingPrefixProbeExecution_eager (limit : Nat) (key : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest) (edgeHigh : GlobalChainEdgeIndex → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) Forgery) (encoding : Encoding) :
    (simulateQ (eagerTraceImpl base) (limitedEncodingPrefixProbeExecution limit key edgeHigh computation encoding)).run =
      appendLimitedEncodingPrefixProbe base key encoding <$>
        (simulateQ (eagerTraceImpl base) (limitedFirstLanePrefix limit key edgeHigh computation
          (GlobalHighDirectTracedState.initial (globalFilteredCausalKeygenState key)) ⟨0, 0, 0⟩)).run := by
  unfold limitedEncodingPrefixProbeExecution
  simp only [simulateQ_bind, WriterT.run_bind', map_eq_bind_pure_comp]
  apply bind_congr
  rintro ⟨⟨completed, counters⟩, trace⟩
  cases completed with
  | none => simp [appendLimitedEncodingPrefixProbe, Prod.map]
  | some completed =>
      simp only [simulateQ_bind, WriterT.run_bind', publicDecidingProbe_eager,
        pure_bind, simulateQ_pure, WriterT.run_pure, map_pure]
      simp [appendLimitedEncodingPrefixProbe, Prod.map]

theorem appendLimitedEncodingPrefixProbe_preserves_hit (base : GlobalChainValueIndex → Digest)
    (key : ProgrammedGlobalChainKeygenView) (encoding : Encoding)
    (result : LimitedPrefixResult × ActionTrace GlobalChainValueIndex)
    (hhit : CombinedHit base result.2) :
    CombinedHit base (appendLimitedEncodingPrefixProbe base key encoding result).2 := by
  unfold appendLimitedEncodingPrefixProbe
  split
  · exact hhit
  · exact CombinedHit.append_of_prefix base _ _ hhit

theorem hazardCount_appendLimitedEncodingPrefixProbe_le (base : GlobalChainValueIndex → Digest)
    (key : ProgrammedGlobalChainKeygenView) (encoding : Encoding)
    (result : LimitedPrefixResult × ActionTrace GlobalChainValueIndex) :
    hazardCount (appendLimitedEncodingPrefixProbe base key encoding result).2 ≤ hazardCount result.2 + 1 := by
  unfold appendLimitedEncodingPrefixProbe
  split
  · exact Nat.le_add_right _ _
  · simp only [hazardCount_append, decidingProbeResult_hazardCount, le_refl]

theorem limitedEncodingPrefixProbe_trace_bound
    (table : GlobalChainValueIndex → Digest) (limit : Nat) (key : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (computation : OracleComp (OracleWorld + SigningSpec) Forgery)
    (encoding : Encoding) (result : LimitedPrefixResult × ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support (simulateQ (eagerTraceImpl table)
      (limitedEncodingPrefixProbeExecution limit key edgeHigh computation encoding)).run) :
    hazardCount result.2 ≤ limit + 1 := by
  rw [limitedEncodingPrefixProbeExecution_eager, support_map] at hresult
  obtain ⟨prefixResult, hprefix, rfl⟩ := hresult
  have hbudget := limitedFirstLanePrefix_trace_budget table limit key edgeHigh computation
    (GlobalHighDirectTracedState.initial (globalFilteredCausalKeygenState key)) ⟨0, 0, 0⟩
    (by simp [EncodingBudgetCounters.charge]) prefixResult hprefix
  have hcount := limitedFirstLanePrefix_trace_direct table limit key edgeHigh computation
    (GlobalHighDirectTracedState.initial (globalFilteredCausalKeygenState key)) ⟨0, 0, 0⟩ prefixResult hprefix
  have hdirect : prefixResult.1.2.direct ≤ limit := (Nat.le_add_right _ _).trans hbudget.1
  exact (hazardCount_appendLimitedEncodingPrefixProbe_le table key encoding prefixResult).trans
    (Nat.add_le_add_right (by simpa only [Nat.zero_add] using hcount.trans hdirect) 1)

theorem limitedRevealedEncodingPrefixEvent_coupling
    (left : ProgrammedGlobalChainKeygenView) (right : BaseHighKey)
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleft : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hright : right.1.1 ∈ support trajectoryProgrammedGlobalChainKeygen)
    (limit : Nat) (computation : OracleComp (OracleWorld + SigningSpec) Forgery)
    (hbudget : CountedSourceBudget (Concrete.materializePrecomputation left.cache left.secretKey)
      limit computation (CountedSourceState.initial left.cache)) (encoding : Encoding) :
    RelTriple
      ((simulateQ (countedSourceImpl (Concrete.materializePrecomputation left.cache left.secretKey))
        computation).run (CountedSourceState.initial left.cache))
      ((simulateQ (eagerTraceImpl right.1.2)
        (limitedEncodingPrefixProbeExecution limit right.1.1 right.2 computation encoding)).run)
      (fun source target => RevealedEncodingPrefixEvent left (source.1, source.2.toSource) encoding →
        CombinedHit right.1.2 target.2) := by
  rw [limitedEncodingPrefixProbeExecution_eager, ← id_map
    ((simulateQ (countedSourceImpl (Concrete.materializePrecomputation left.cache left.secretKey))
      computation).run (CountedSourceState.initial left.cache))]
  apply relTriple_map
  apply relTriple_post_mono (relTriple_with_support
    (relTriple_countedSource_limitedPrefix left right hrel hleft hright limit computation hbudget))
  intro source target hresult hevent
  obtain ⟨⟨_hsourceBudget, _htargetBudget, _hsamples, _hhazards, hrelation⟩, _hsource, htarget⟩ := hresult
  rcases hrelation with ⟨state, hvalue, hgood, _hcounters, _hcount⟩ | hhit
  · simp only [List.nil_append] at hgood
    have hcovered := limitedFirstLanePrefix_returnedCovered right.1.2 limit right.1.1 right.2
      computation ⟨0, 0, 0⟩ target (source.1, state) htarget hvalue
    change CombinedHit right.1.2 (appendLimitedEncodingPrefixProbe right.1.2 right.1.1 encoding target).2
    simp only [appendLimitedEncodingPrefixProbe, hvalue]
    exact revealedEncodingPrefixEvent_good_implies_hit left right hrel hleft hright
      (source.1, source.2.toSource) ((source.1, state), target.2) rfl hgood hcovered encoding hevent
  · exact appendLimitedEncodingPrefixProbe_preserves_hit right.1.2 right.1.1 encoding target
      (by simpa only [List.nil_append] using hhit)

noncomputable def publicLimitedEncodingPrefixProbeExecution (limit : Nat) (adversary : Adversary)
    (encoding : Encoding) (key : ProgrammedGlobalChainKeygenView) (edgeHigh : GlobalChainEdgeIndex → Digest) :
    OracleComp GlobalFirstLaneWorld LimitedPrefixResult :=
  limitedEncodingPrefixProbeExecution limit key edgeHigh (adversary.main key.publicKey) encoding

theorem coupledLimitedEncodingProbe_hit_probability_le (limit : Nat) (adversary : Adversary)
    (encoding : Encoding) :
    Pr[CoupledLimitedPrefixHit |
      coupledFirstLaneProgram (publicLimitedEncodingPrefixProbeExecution limit adversary encoding)] ≤
      ((limit : ℝ≥0∞) + 1) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  calc
    _ = Pr[fun result => CombinedHit result.1.1.2 (enforceHazardTrace (limit + 1) result.2.2) |
        coupledFirstLaneProgram (publicLimitedEncodingPrefixProbeExecution limit adversary encoding)] := by
      apply probEvent_congr' (fun result hresult => ?_) rfl
      unfold coupledFirstLaneProgram at hresult
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hresult
      obtain ⟨key, _, outcome, houtcome, rfl⟩ := hresult
      rw [enforceHazardTrace_eq_self_of_count_le _ _
        (limitedEncodingPrefixProbe_trace_bound key.1.2 limit key.1.1 key.2
          (adversary.main key.1.1.publicKey) encoding outcome houtcome)]
      rfl
    _ ≤ ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ * expectedCoupledHazards (limit + 1)
        (publicLimitedEncodingPrefixProbeExecution limit adversary encoding) :=
      coupled_enforcedHit_probability_le_expected (limit + 1) _
    _ ≤ _ := by
      simpa only [Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_comm] using
        mul_le_mul' (le_refl (((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹)) (expectedCoupledHazards_le (limit + 1) _)

theorem revealedEncodingPrefixEvent_probability_le (adversary : Adversary) (limit : Nat)
    (hbudget : ∀ key ∈ support trajectoryProgrammedGlobalChainKeygen,
      CountedSourceBudget (Concrete.materializePrecomputation key.cache key.secretKey)
        limit (adversary.main key.publicKey) (CountedSourceState.initial key.cache)) (encoding : Encoding) :
    Pr[fun result => RevealedEncodingPrefixEvent result.1 result.2 encoding | sourcePrefixProgram adversary] ≤
      ((limit : ℝ≥0∞) + 1) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  rw [← sourceCountedPrefixProgram_source_projection, probEvent_map]
  apply le_trans _ (coupledLimitedEncodingProbe_hit_probability_le limit adversary encoding)
  apply probEvent_le_of_relTriple (show RelTriple (sourceCountedPrefixProgram adversary)
    (coupledFirstLaneProgram (publicLimitedEncodingPrefixProbeExecution limit adversary encoding))
    (fun source target => RevealedEncodingPrefixEvent source.1 (source.2.1, source.2.2.toSource) encoding →
      CoupledLimitedPrefixHit target) from ?_)
  · intro source target hpost hevent
    exact hpost hevent
  · unfold sourceCountedPrefixProgram coupledFirstLaneProgram
    apply relTriple_bind (relTriple_with_support relTriple_trajectoryProgrammedGlobalChainKeygen_withBaseHigh_stable)
    intro left right hkeys
    obtain ⟨hrel, hleft, hright⟩ := hkeys
    have h := limitedRevealedEncodingPrefixEvent_coupling left right hrel hleft
      (coupledGlobalChainKeygenWithBaseHighFull_support_keyView right hright) limit
      (adversary.main left.publicKey) (hbudget left hleft) encoding
    have hpk : left.publicKey = right.1.1.publicKey := hrel.1.toStable.1.2.1
    change RelTriple (sourceCountedPrefixExecution adversary left)
      ((simulateQ (eagerTraceImpl right.1.2) (limitedEncodingPrefixProbeExecution limit right.1.1 right.2
        (adversary.main left.publicKey) encoding)).run) _ at h
    rw [hpk] at h
    apply relTriple_bind h
    intro source target hpost
    exact relTriple_pure_pure hpost

/-- info: 'XmssSecurity.TargetSum.Deciding.revealedEncodingPrefixEvent_probability_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms revealedEncodingPrefixEvent_probability_le

end XmssSecurity.TargetSum.Deciding
