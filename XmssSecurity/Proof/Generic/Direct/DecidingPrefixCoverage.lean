import XmssSecurity.Proof.Generic.Direct.DecidingFirstLaneCoupling

/-! Every chain value revealed before verification belongs to a returned signature's suffix. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.Generic.CappedChain

variable [Code]

theorem globalMonitoredAdversary_support_returnedCovered
    (right : ProgrammedGlobalChainKeygenView × (GlobalChainValueIndex → Digest))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (result : α × GlobalMonitoredTracedState)
    (hresult : result ∈ support
      ((simulateQ (globalMonitoredMappedAdversaryImpl right) computation).run
        (⟨globalFilteredCausalKeygenState right.1, []⟩, []))) :
    GlobalMonitoredCausalStateCovered
      (GlobalReturnedChainValueCovered result.2.1.causal.cache right.1.secretKey
        result.2.2.toSigningLog) result.2.1 := by
  apply simulate_globalMonitoredMappedAdversary_support_covered_of_final right computation
    (⟨globalFilteredCausalKeygenState right.1, []⟩, [])
    (GlobalReturnedChainValueCovered result.2.1.causal.cache right.1.secretKey
      result.2.2.toSigningLog) result.2.1.causal.cache result.2.2
  · constructor
    · intro index value hrevealed
      simp [globalFilteredCausalKeygenState] at hrevealed
    · simp [GlobalCausalTraceRevealsCovered]
  · exact globalReturnedChainValueCovered_forwardClosed _ _ _
  · intro request signature encoding chain haction hdecode
    exact globalReturnedChainValueCovered_contains_returned _ _ _ request signature encoding
      (result.2.2.sign_mem_toSigningLog request signature haction) hdecode chain
  · exact hresult
  · exact le_rfl
  · exact fun _ hmem => hmem

theorem globalFirstLaneAdversary_support_returnedCovered
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (result : (α × GlobalDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl base)
        ((simulateQ (globalFirstLaneExactTracedMappedAdversaryImpl keyView)
          computation).run
            (GlobalDirectTracedState.initial (globalFilteredCausalKeygenState keyView)))).run)) :
    GlobalCausalTraceRevealsCovered
      (GlobalReturnedChainValueCovered result.1.2.causalState.cache keyView.secretKey
        result.1.2.attackerTrace.toSigningLog) result.2.chainActions := by
  have hmapped : (result.1, result.2.chainActions) ∈ support
      ((fun execution => (execution.1, execution.2.chainActions)) <$>
        (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl base)
          ((simulateQ (globalFirstLaneExactTracedMappedAdversaryImpl keyView)
            computation).run
              (GlobalDirectTracedState.initial (globalFilteredCausalKeygenState keyView)))).run) := by
    rw [support_map]
    exact ⟨result, hresult, rfl⟩
  rw [simulate_globalFirstLaneEagerTrace_chainProjection] at hmapped
  rw [globalFirstLaneErases_simulateQ_run _ _
    (globalFirstLaneErase_exactTracedMappedAdversaryImpl keyView)] at hmapped
  let initial : GlobalMonitoredTracedState :=
    (⟨globalFilteredCausalKeygenState keyView, []⟩, [])
  have hprojection := map_simulate_globalMonitored_adversary_exact keyView base
    computation initial
  simp only [initial, List.nil_append, Prod.eta] at hprojection
  change _ = id <$> _ at hprojection
  rw [id_map] at hprojection
  simp only [GlobalDirectTracedState.initial, GlobalDirectTracedState.mk]
    at hmapped hprojection
  rw [← hprojection, support_map] at hmapped
  obtain ⟨monitoredResult, hmonitoredResult, heq⟩ := hmapped
  have hcovered := (globalMonitoredAdversary_support_returnedCovered
    (keyView, base) computation monitoredResult hmonitoredResult).2
  have hcache := congrArg (fun output => output.1.2.causalState.cache) heq
  have htrace := congrArg (fun output => output.1.2.attackerTrace) heq
  have hchain := congrArg Prod.snd heq
  dsimp only [GlobalDirectTracedState.causalState, GlobalDirectTracedState.attackerTrace]
    at hcache htrace hchain ⊢
  rw [← hcache, ← htrace, ← hchain]
  exact hcovered

end XmssSecurity.Generic.CappedChain
