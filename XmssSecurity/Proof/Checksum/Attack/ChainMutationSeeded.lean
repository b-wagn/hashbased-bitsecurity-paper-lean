import XmssSecurity.Proof.Checksum.Attack.MutationGame
import XmssSecurity.Proof.Checksum.Attack.ChainMutationAccounting
import XmssSecurity.Proof.Checksum.Direct.SeedGuessingZero
import XmssSecurity.Proof.Checksum.Modes.Exact

/-! The one-request mutation attack transfers exactly to the seeded scheme. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.Checksum.Attack

open DeterministicSigning

theorem memoize_liftPrivateSamples {α : Type} (computation : ProbComp α)
    (cache : QueryCache SigningSpec) :
    memoize (liftPrivateSamples computation) cache = liftPrivateSamples computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [liftPrivateSamples, memoize_pure]
  | query_bind input next ih =>
      simp only [liftPrivateSamples, simulateQ_bind, simulateQ_spec_query] at ih ⊢
      rw [memoize_base]
      exact bind_congr ih

theorem memoize_chainMutationMain : memoize chainMutationMain ∅ = chainMutationMain := by
  unfold chainMutationMain
  rw [memoize_request]
  simp only [QueryCache.empty_apply, bind_pure_comp, memoize_map, memoize_liftPrivateSamples]

theorem memoAdversary_chainMutation : Seeded.memoAdversary chainMutationAdversary = chainMutationAdversary := by
  unfold Seeded.memoAdversary chainMutationAdversary
  congr 1
  funext publicKey
  exact memoize_chainMutationMain

theorem chainMutation_seeded_advantage_eq_reference :
    forgeAdvantage Seeded.scheme chainMutationAdversary =
      forgeAdvantage Concrete.scheme chainMutationAdversary := by
  unfold forgeAdvantage
  apply probOutput_congr rfl
  calc
    _ = evalDist (Seeded.independentTableGame chainMutationAdversary) :=
      Seeded.evalDist_deterministic_eq_table_of_direct_zero chainMutationAdversary chainMutation_direct_zero
    _ = _ := by
      simpa only [memoAdversary_chainMutation] using
        Seeded.evalDist_independentTableGame_memo chainMutationAdversary

theorem chainMutation_seeded_advantage_exceeds_123 :
    (1 : ℝ≥0∞) / ((2 ^ 123 : ℕ) : ℝ≥0∞) <
      forgeAdvantage Seeded.scheme chainMutationAdversary := by
  rw [chainMutation_seeded_advantage_eq_reference]
  exact chainMutation_reference_advantage_exceeds_123

theorem chainMutation_requests_attack : ¬(SUFCMA.notion ⟨false, false, false, true⟩).HasClassicalSecurityBits xmss (122 + 1) :=
  requests_attack_of_chainMutation_advantage chainMutation_seeded_advantage_exceeds_123

/-- info: 'XmssSecurity.Checksum.Attack.chainMutation_requests_attack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms chainMutation_requests_attack

end XmssSecurity.Checksum.Attack
