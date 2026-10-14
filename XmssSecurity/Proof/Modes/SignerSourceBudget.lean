import XmssSecurity.Proof.Modes.SignerPhaseCounts
import XmssSecurity.Proof.Direct.CountedSourceTrace

/-! Apply the statement's budget to the source experiment whose traces are used in the
first-lane coupling. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.Modes

open Seeded DeterministicSigning CappedChain

theorem simulate_withRequestLog_forget {α σ : Type}
    (implementation : QueryImpl (OracleWorld + SigningSpec) (StateT σ ProbComp))
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : σ) :
    (fun result => (result.1.1, result.2)) <$>
      (simulateQ implementation (withRequestLog computation)).run state =
        (simulateQ implementation computation).run state := by
  have h := congrArg (fun body : OracleComp (OracleWorld + SigningSpec) α =>
    (simulateQ implementation body).run state) (fst_withRequestLog computation)
  simpa only [simulateQ_map, StateT.run_map] using h

theorem signer_referencePhaseCounts_unlogged_bound
    (adversary : Security.StatementAdversary) (q : Nat) (hsmall : q < 2 ^ 256)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound xmss adversary q)
    (keyResult : (PublicKey × XmssSecurity.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (result : Forgery × PhaseCounts)
    (hresult : result ∈ support ((simulateQ (referencePhaseCountsImpl keyResult.1.2)
      (memoize (adversary.main keyResult.1.1) ∅)).run ⟨keyResult.2, 0, 0⟩)) :
    result.2.direct + 2 * result.2.signing ≤ q := by
  rw [← simulate_withRequestLog_forget (referencePhaseCountsImpl keyResult.1.2)
    (memoize (adversary.main keyResult.1.1) ∅) ⟨keyResult.2, 0, 0⟩, support_map] at hresult
  obtain ⟨logged, hlogged, rfl⟩ := hresult
  exact signer_referencePhaseCounts_bound adversary q hsmall hbound keyResult hkey logged hlogged

theorem signer_countedSource_bound_after_keygen
    (adversary : Security.StatementAdversary) (q : Nat) (hsmall : q < 2 ^ 256)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound xmss adversary q)
    (keyResult : (PublicKey × XmssSecurity.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (result : Forgery × CountedSourceState)
    (hresult : result ∈ support ((simulateQ (countedSourceImpl keyResult.1.2)
      (memoize (adversary.main keyResult.1.1) ∅)).run
        (CountedSourceState.initial keyResult.2))) :
    result.2.counts.direct + 2 * result.2.counts.signing ≤ q := by
  apply signer_referencePhaseCounts_unlogged_bound adversary q hsmall hbound keyResult hkey
    (result.1, result.2.counts)
  have hproject := countedSource_counts_projection keyResult.1.2
    (memoize (adversary.main keyResult.1.1) ∅) (CountedSourceState.initial keyResult.2)
  dsimp only [CountedSourceState.initial] at hproject
  rw [← hproject, support_map]
  exact ⟨result, hresult, rfl⟩

/-- info: 'XmssSecurity.Modes.signer_countedSource_bound_after_keygen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signer_countedSource_bound_after_keygen

end XmssSecurity.Modes
