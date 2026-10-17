import XmssSecurity.Proof.TargetSum.Direct.LimitedEncodingProbe

/-! Bound fresh revealed deciding values by conditioning the final hash on
acceptance and applying the supplied-encoding prefix probe bound. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.TargetSum.Deciding

open CappedChain FirstLaneOracleSimulation

abbrev AcceptedEncodingPrefixResult :=
  (ProgrammedGlobalChainKeygenView × (Forgery × SourceExactTracedState)) × TargetSum.AcceptedHashOutput

theorem acceptedFreshRevealedProbability_le (adversary : Adversary) (limit : Nat)
    (hbudget : ∀ key ∈ support trajectoryProgrammedGlobalChainKeygen,
      CountedSourceBudget (Concrete.materializePrecomputation key.cache key.secretKey)
        limit (adversary.main key.publicKey) (CountedSourceState.initial key.cache)) :
    acceptedFreshRevealedProbability adversary ≤
      ((limit : ℝ≥0∞) + 1) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  let sampled : ProbComp AcceptedEncodingPrefixResult := do
    let prefixPair ← sourcePrefixProgram adversary
    let output ← ($ᵗ TargetSum.AcceptedHashOutput)
    pure (prefixPair, output)
  have heq : acceptedFreshRevealedProbability adversary =
      Pr[fun result => SourcePrefixForgedEncodingFresh result.1 ∧
          SourceWinningRevealedEvent (result.1.1, result.2) | sampled >>= fun pair => do
        let result ← sourcePrefixFinishAfterHash pair.1.1 pair.1.2 pair.2.1
        pure (pair.1, result)] := by
    simp only [sampled, acceptedFreshRevealedProbability, bind_assoc, pure_bind]
  rw [heq]
  calc
    _ ≤ Pr[fun pair : AcceptedEncodingPrefixResult => RevealedEncodingPrefixEvent pair.1.1 pair.1.2
        (TargetSum.acceptedHashEncoding pair.2) | sampled] := by
      apply probEvent_bind_le_probEvent (mx := sampled)
      intro pair hpair hnone
      dsimp only [sampled] at hpair
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hpair
      obtain ⟨prefixPair, hprefixPair, output, _, rfl⟩ := hpair
      unfold sourcePrefixProgram at hprefixPair
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hprefixPair
      obtain ⟨key, hkey, prefixResult, hprefix, rfl⟩ := hprefixPair
      apply probEvent_eq_zero
      intro result hresult hevent
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hresult
      obtain ⟨execution, hfinish, rfl⟩ := hresult
      exact hnone (sourcePrefixFinishAfterHash_revealed_implies_prefixEvent adversary key hkey
        prefixResult hprefix output hevent.1 execution hfinish hevent.2)
    _ = Pr[fun pair : AcceptedEncodingPrefixResult => RevealedEncodingPrefixEvent pair.1.1 pair.1.2
        (TargetSum.acceptedHashEncoding pair.2) | do
          let output ← ($ᵗ TargetSum.AcceptedHashOutput)
          let prefixPair ← sourcePrefixProgram adversary
          pure (prefixPair, output)] := by
      apply probEvent_eq_of_evalDist_eq
      exact OracleComp.DeferredSampling.evalDist_bind_comm
        (sourcePrefixProgram adversary) ($ᵗ TargetSum.AcceptedHashOutput)
        (fun prefixPair output => pure (prefixPair, output))
    _ ≤ _ := by
      apply probEvent_bind_le_of_forall_le
      intro output _
      simp only [bind_pure_comp, probEvent_map, Function.comp_def]
      exact revealedEncodingPrefixEvent_probability_le adversary limit hbudget
        (TargetSum.acceptedHashEncoding output)

theorem freshRevealedProbability_le (adversary : Adversary) (limit : Nat)
    (hbudget : ∀ key ∈ support trajectoryProgrammedGlobalChainKeygen,
      CountedSourceBudget (Concrete.materializePrecomputation key.cache key.secretKey)
        limit (adversary.main key.publicKey) (CountedSourceState.initial key.cache)) :
    freshRevealedProbability adversary ≤
      TargetSum.acceptanceProbability * (((limit : ℝ≥0∞) + 1) / ((2 ^ digestBits : Nat) : ℝ≥0∞)) := by
  rw [freshRevealedProbability_eq_acceptance_mul]
  exact mul_le_mul' le_rfl (acceptedFreshRevealedProbability_le adversary limit hbudget)

/-- info: 'XmssSecurity.TargetSum.Deciding.freshRevealedProbability_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms freshRevealedProbability_le

end XmssSecurity.TargetSum.Deciding
