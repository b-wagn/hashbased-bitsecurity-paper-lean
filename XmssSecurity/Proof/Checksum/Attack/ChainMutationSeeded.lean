import XmssSecurity.Proof.Checksum.Attack.MutationGame
import XmssSecurity.Proof.Generic.Attack.ChainMutationAccounting
import XmssSecurity.Proof.Generic.Direct.SeedGuessingZero
import XmssSecurity.Proof.Generic.Modes.Exact
import XmssSecurity.Proof.Checksum.Code
import XmssSecurity.Proof.Checksum.EncodingProbability
/-! The one-request mutation attack transfers exactly to the seeded scheme. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.Checksum.Attack

open Generic.DeterministicSigning

theorem memoize_liftPrivateSamples {α : Type} (computation : ProbComp α)
    (cache : QueryCache Generic.SigningSpec) :
    Generic.DeterministicSigning.memoize (Generic.Attack.liftPrivateSamples computation) cache = Generic.Attack.liftPrivateSamples computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [Generic.Attack.liftPrivateSamples, Generic.DeterministicSigning.memoize_pure]
  | query_bind input next ih =>
      simp only [Generic.Attack.liftPrivateSamples, simulateQ_bind, simulateQ_spec_query] at ih ⊢
      rw [Generic.DeterministicSigning.memoize_base]
      exact bind_congr ih

theorem memoize_chainMutationMain : Generic.DeterministicSigning.memoize Generic.Attack.chainMutationMain ∅ = Generic.Attack.chainMutationMain := by
  unfold Generic.Attack.chainMutationMain
  rw [Generic.DeterministicSigning.memoize_request]
  simp only [QueryCache.empty_apply, bind_pure_comp, Generic.DeterministicSigning.memoize_map, memoize_liftPrivateSamples]

theorem memoAdversary_chainMutation : Generic.Seeded.memoAdversary Generic.Attack.chainMutationAdversary = Generic.Attack.chainMutationAdversary := by
  unfold Generic.Seeded.memoAdversary Generic.Attack.chainMutationAdversary
  congr 1
  funext publicKey
  exact memoize_chainMutationMain

theorem chainMutation_seeded_advantage_eq_reference :
    Generic.forgeAdvantage Generic.Seeded.scheme Generic.Attack.chainMutationAdversary =
      Generic.forgeAdvantage Generic.Concrete.scheme Generic.Attack.chainMutationAdversary := by
  unfold Generic.forgeAdvantage
  apply probOutput_congr rfl
  calc
    _ = evalDist (Generic.Seeded.independentTableGame Generic.Attack.chainMutationAdversary) :=
      Generic.Seeded.evalDist_deterministic_eq_table_of_direct_zero Generic.Attack.chainMutationAdversary Generic.Attack.chainMutation_direct_zero
    _ = _ := by
      simpa only [memoAdversary_chainMutation] using
        Generic.Seeded.evalDist_independentTableGame_memo Generic.Attack.chainMutationAdversary

theorem chainMutation_seeded_advantage_exceeds_123 :
    (1 : ℝ≥0∞) / ((2 ^ 123 : ℕ) : ℝ≥0∞) <
      Generic.forgeAdvantage Generic.Seeded.scheme Generic.Attack.chainMutationAdversary := by
  rw [chainMutation_seeded_advantage_eq_reference]
  exact chainMutation_reference_advantage_exceeds_123

theorem chainMutation_requests_attack : ¬(SUFCMA.notion ⟨false, false, false, true⟩).HasClassicalSecurityBits Generic.xmss (122 + 1) :=
  Generic.Attack.requests_attack_of_chainMutation_advantage chainMutation_seeded_advantage_exceeds_123

/-- info: 'XmssSecurity.Checksum.Attack.chainMutation_requests_attack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms chainMutation_requests_attack

end XmssSecurity.Checksum.Attack
