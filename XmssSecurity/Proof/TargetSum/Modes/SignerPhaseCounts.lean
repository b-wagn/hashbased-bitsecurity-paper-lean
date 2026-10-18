import XmssSecurity.Proof.TargetSum.Modes.SignerReferenceBudget
import XmssSecurity.Proof.TargetSum.Deterministic.PhaseCounts

/-! The reference phase shares one budget between direct hashes and signing attempts. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Modes
open XmssSecurity.Modes

open Seeded DeterministicSigning

theorem signer_referencePhaseCounts_bound
    (adversary : Security.StatementAdversary) (q : Nat) (hsmall : q < 2 ^ 256)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound xmss adversary q)
    (keyResult : (PublicKey × XmssSecurity.TargetSum.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (result : (Forgery × QueryLog SigningSpec) × PhaseCounts)
    (hresult : result ∈ support ((simulateQ (referencePhaseCountsImpl keyResult.1.2)
      (withRequestLog (memoize (adversary.main keyResult.1.1) ∅))).run
        ⟨keyResult.2, 0, 0⟩)) :
    result.2.direct + 2 * result.2.signing ≤ q := by
  apply signer_referencePhaseCost_le_after_keygen adversary q hsmall hbound keyResult hkey
    (result.1, result.2.weighted 2)
  have hproject := referencePhaseCounts_cost_projection keyResult.1.2
    (withRequestLog (memoize (adversary.main keyResult.1.1) ∅)) ⟨keyResult.2, 0, 0⟩
  simp only [PhaseCounts.weighted, Nat.mul_zero, Nat.zero_add] at hproject
  rw [← hproject, support_map]
  exact ⟨result, hresult, rfl⟩

/-- info: 'XmssSecurity.TargetSum.Modes.signer_referencePhaseCounts_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signer_referencePhaseCounts_bound

end XmssSecurity.TargetSum.Modes
