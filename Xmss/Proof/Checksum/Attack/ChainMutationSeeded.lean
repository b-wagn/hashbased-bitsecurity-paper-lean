import Xmss.Proof.Checksum.Attack.MutationGame
import Xmss.Proof.Generic.Attack.ChainMutationAccounting
import Xmss.Proof.Generic.Direct.SeedGuessingZero
import Xmss.Proof.Generic.Modes.Exact
import Xmss.Proof.Checksum.Code
import Xmss.Proof.Checksum.EncodingProbability
/-! The one-request mutation attack transfers exactly to the seeded scheme. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

open Xmss.Generic

namespace Xmss.Checksum.Attack

open DeterministicSigning

theorem memoize_liftPrivateSamples {α : Type} (computation : ProbComp α)
    (cache : QueryCache SigningSpec) :
    DeterministicSigning.memoize (Attack.liftPrivateSamples computation) cache = Attack.liftPrivateSamples computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [Attack.liftPrivateSamples, DeterministicSigning.memoize_pure]
  | query_bind input next ih =>
      simp only [Attack.liftPrivateSamples, simulateQ_bind, simulateQ_spec_query] at ih ⊢
      rw [DeterministicSigning.memoize_base]
      exact bind_congr ih

theorem memoize_chainMutationMain : DeterministicSigning.memoize Attack.chainMutationMain ∅ = Attack.chainMutationMain := by
  unfold Attack.chainMutationMain
  rw [DeterministicSigning.memoize_request]
  simp only [QueryCache.empty_apply, bind_pure_comp, DeterministicSigning.memoize_map, memoize_liftPrivateSamples]

theorem memoAdversary_chainMutation : Seeded.memoAdversary Attack.chainMutationAdversary = Attack.chainMutationAdversary := by
  unfold Seeded.memoAdversary Attack.chainMutationAdversary
  congr 1
  funext publicKey
  exact memoize_chainMutationMain

theorem chainMutation_seeded_advantage_eq_reference :
    forgeAdvantage Seeded.scheme Attack.chainMutationAdversary =
      forgeAdvantage precomputedScheme Attack.chainMutationAdversary := by
  unfold forgeAdvantage
  apply probOutput_congr rfl
  calc
    _ = evalDist (Seeded.independentTableGame Attack.chainMutationAdversary) :=
      Seeded.evalDist_deterministic_eq_table_of_direct_zero Attack.chainMutationAdversary Attack.chainMutation_direct_zero
    _ = _ := by
      simpa only [memoAdversary_chainMutation] using
        Seeded.evalDist_independentTableGame_memo Attack.chainMutationAdversary

theorem chainMutation_seeded_advantage_exceeds_123 :
    (1 : ℝ≥0∞) / ((2 ^ 123 : ℕ) : ℝ≥0∞) <
      forgeAdvantage Seeded.scheme Attack.chainMutationAdversary := by
  rw [chainMutation_seeded_advantage_eq_reference]
  exact chainMutation_reference_advantage_exceeds_123

theorem chainMutation_requests_attack : ¬(SUFCMA.notion ⟨false, false, false, true⟩).HasClassicalSecurityBits Generic.xmss (122 + 1) :=
  Attack.requests_attack_of_chainMutation_advantage chainMutation_seeded_advantage_exceeds_123

/-- info: 'Xmss.Checksum.Attack.chainMutation_requests_attack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms chainMutation_requests_attack

end Xmss.Checksum.Attack
