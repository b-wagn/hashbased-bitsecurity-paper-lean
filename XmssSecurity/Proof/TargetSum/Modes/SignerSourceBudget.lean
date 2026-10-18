import XmssSecurity.Proof.TargetSum.Modes.SignerPhaseCounts
import XmssSecurity.Proof.TargetSum.Direct.CountedSourceBudget
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Apply the statement's budget to the source experiment whose traces are used in the
first-lane coupling. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Modes
open XmssSecurity.Modes

open Seeded Generic.DeterministicSigning CappedChain

theorem simulate_withRequestLog_forget {α σ : Type}
    (implementation : QueryImpl (OracleWorld + Generic.SigningSpec) (StateT σ ProbComp))
    (computation : OracleComp (OracleWorld + Generic.SigningSpec) α) (state : σ) :
    (fun result => (result.1.1, result.2)) <$>
      (simulateQ implementation (Generic.DeterministicSigning.withRequestLog computation)).run state =
        (simulateQ implementation computation).run state := by
  have h := congrArg (fun body : OracleComp (OracleWorld + Generic.SigningSpec) α =>
    (simulateQ implementation body).run state) (Generic.DeterministicSigning.fst_withRequestLog computation)
  simpa only [simulateQ_map, StateT.run_map] using h

theorem signer_referencePhaseCounts_unlogged_bound
    (adversary : Generic.Security.StatementAdversary) (q : Nat) (hsmall : q < 2 ^ 256)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound Generic.xmss adversary q)
    (keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ Generic.romImpl Generic.Concrete.scheme.keygen).run ∅))
    (result : Generic.Forgery × PhaseCounts)
    (hresult : result ∈ support ((simulateQ (referencePhaseCountsImpl keyResult.1.2)
      (Generic.DeterministicSigning.memoize (adversary.main keyResult.1.1) ∅)).run ⟨keyResult.2, 0, 0⟩)) :
    result.2.direct + 2 * result.2.signing ≤ q := by
  rw [← simulate_withRequestLog_forget (referencePhaseCountsImpl keyResult.1.2)
    (Generic.DeterministicSigning.memoize (adversary.main keyResult.1.1) ∅) ⟨keyResult.2, 0, 0⟩, support_map] at hresult
  obtain ⟨logged, hlogged, rfl⟩ := hresult
  exact signer_referencePhaseCounts_bound adversary q hsmall hbound keyResult hkey logged hlogged

theorem signer_countedSource_bound_after_keygen
    (adversary : Generic.Security.StatementAdversary) (q : Nat) (hsmall : q < 2 ^ 256)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound Generic.xmss adversary q)
    (keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ Generic.romImpl Generic.Concrete.scheme.keygen).run ∅))
    (result : Generic.Forgery × CountedSourceState)
    (hresult : result ∈ support ((simulateQ (countedSourceImpl keyResult.1.2)
      (Generic.DeterministicSigning.memoize (adversary.main keyResult.1.1) ∅)).run
        (CountedSourceState.initial keyResult.2))) :
    result.2.counts.direct + 2 * result.2.counts.signing ≤ q := by
  apply signer_referencePhaseCounts_unlogged_bound adversary q hsmall hbound keyResult hkey
    (result.1, result.2.counts)
  have hproject := countedSource_counts_projection keyResult.1.2
    (Generic.DeterministicSigning.memoize (adversary.main keyResult.1.1) ∅) (CountedSourceState.initial keyResult.2)
  dsimp only [CountedSourceState.initial] at hproject
  rw [← hproject, support_map]
  exact ⟨result, hresult, rfl⟩

theorem signer_countedSourceBudget_after_keygen
    (adversary : Generic.Security.StatementAdversary) (q : Nat) (hsmall : q < 2 ^ 256)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound Generic.xmss adversary q)
    (keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ Generic.romImpl Generic.Concrete.scheme.keygen).run ∅)) :
    CountedSourceBudget keyResult.1.2 q (Generic.DeterministicSigning.memoize (adversary.main keyResult.1.1) ∅)
      (CountedSourceState.initial keyResult.2) :=
  signer_countedSource_bound_after_keygen adversary q hsmall hbound keyResult hkey

theorem signer_countedSourceBudget_after_trajectory
    (adversary : Generic.Security.StatementAdversary) (q : Nat) (hsmall : q < 2 ^ 256)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound Generic.xmss adversary q)
    (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView)
    (hkey : key ∈ support Generic.CappedChain.trajectoryProgrammedGlobalChainKeygen) :
    CountedSourceBudget (Generic.Concrete.materializePrecomputation key.cache key.secretKey) q
      (Generic.DeterministicSigning.memoize (adversary.main key.publicKey) ∅) (CountedSourceState.initial key.cache) := by
  apply signer_countedSourceBudget_after_keygen adversary q hsmall hbound
    (Generic.Concrete.materializeCachedKeyResult key.keyResult)
  apply (mem_support_iff_of_evalDist_eq
    Generic.CappedChain.evalDist_materializedTrajectoryGlobalChainKeygen_eq_cappedKeygen _).mp
  rw [support_map]
  exact ⟨key, hkey, rfl⟩

/-- info: 'XmssSecurity.TargetSum.Modes.signer_countedSource_bound_after_keygen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signer_countedSource_bound_after_keygen

/-- info: 'XmssSecurity.TargetSum.Modes.signer_countedSourceBudget_after_trajectory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signer_countedSourceBudget_after_trajectory

end XmssSecurity.TargetSum.Modes
