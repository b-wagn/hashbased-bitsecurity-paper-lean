import XmssSecurity.Proof.TargetSum.Attack.NeighborGame
import XmssSecurity.Proof.Generic.Direct.SeedGuessingZero
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability
/-! Exact transfer of the neighboring-signature attack to deterministic seeded signing. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.TargetSum.Attack

open Generic.DeterministicSigning

theorem memoize_liftWorldToAdversary {α : Type} (computation : OracleComp OracleWorld α)
    (cache : QueryCache Generic.SigningSpec) :
    Generic.DeterministicSigning.memoize (liftWorldToAdversary computation) cache = liftWorldToAdversary computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [liftWorldToAdversary, Generic.DeterministicSigning.memoize_pure]
  | query_bind input next ih =>
      simp only [liftWorldToAdversary, simulateQ_bind, simulateQ_spec_query] at ih ⊢
      rw [Generic.DeterministicSigning.memoize_base]
      exact bind_congr ih

theorem memoize_neighborMain (publicKey : PublicKey) :
    Generic.DeterministicSigning.memoize (neighborMain publicKey) ∅ = neighborMain publicKey := by
  unfold neighborMain
  rw [Generic.DeterministicSigning.memoize_request]
  simp only [QueryCache.empty_apply, bind_pure_comp, Generic.DeterministicSigning.memoize_map, memoize_liftWorldToAdversary]

theorem memoAdversary_neighbor : Generic.Seeded.memoAdversary neighborAdversary = neighborAdversary := by
  unfold Generic.Seeded.memoAdversary neighborAdversary
  congr 1
  funext publicKey
  exact memoize_neighborMain publicKey

theorem tableGameRest_neighbor_noSeed (randomizers : Generic.Seeded.RandomizerOutputs)
    (publicKey : PublicKey) (secretKey : Generic.SecretKey) :
    (Generic.Seeded.gameRest (Generic.Seeded.tableScheme randomizers) neighborAdversary publicKey secretKey).IsQueryBoundP
      (Generic.Seeded.hashBad Generic.MaySeedHit) 0 := by
  rw [neighbor_gameRest]
  refine OracleComp.isQueryBoundP_bind (m := 0)
    (Generic.Seeded.liftM_hash_noSeed _ (Generic.Seeded.tableSign_noSeed _ _ _ _)) ?_
  intro answer _
  refine OracleComp.isQueryBoundP_bind (m := 0) (neighborAfterSigning_noSeed publicKey answer) ?_
  intro signature _
  exact Generic.Seeded.liftM_hash_noSeed _ (Generic.Concrete.verify_noSeed _ _ _ _)

theorem tableGameAfterSecrets_neighbor_noSeed (parameter : PublicParameter)
    (secret : Generic.Seeded.ChainSecrets) (randomizers : Generic.Seeded.RandomizerOutputs) :
    (Generic.Seeded.tableGameAfterSecrets neighborAdversary parameter secret randomizers).IsQueryBoundP
      (Generic.Seeded.hashBad Generic.MaySeedHit) 0 := by
  unfold Generic.Seeded.tableGameAfterSecrets
  refine OracleComp.isQueryBoundP_bind (m := 0) (Generic.Seeded.liftM_hash_noSeed _ ?_)
    (fun result _ => tableGameRest_neighbor_noSeed randomizers _ _)
  rw [withQueryLog, OracleComp.isQueryBoundP_iff_of_map_eq (QueryImpl.fst_map_run_withLogging _ _),
    simulateQ_ofLift_eq_self]
  exact Generic.Concrete.treeNode_noSeed _ _ _ _

theorem neighbor_seeded_advantage_eq_reference :
    Generic.forgeAdvantage Generic.Seeded.scheme neighborAdversary = Generic.forgeAdvantage Generic.Concrete.scheme neighborAdversary := by
  unfold Generic.forgeAdvantage
  apply probOutput_congr rfl
  calc
    _ = evalDist (Generic.Seeded.independentTableGame neighborAdversary) :=
      Generic.Seeded.evalDist_deterministic_eq_table_of_noSeed neighborAdversary tableGameAfterSecrets_neighbor_noSeed
    _ = _ := by
      simpa only [memoAdversary_neighbor] using Generic.Seeded.evalDist_independentTableGame_memo neighborAdversary

theorem neighbor_seeded_advantage_exceeds_five_sixtyfourths :
    5 / 64 < Generic.forgeAdvantage Generic.Seeded.scheme neighborAdversary := by
  rw [neighbor_seeded_advantage_eq_reference]
  exact neighbor_reference_advantage_exceeds_five_sixtyfourths

/-- info: 'XmssSecurity.TargetSum.Attack.neighbor_seeded_advantage_exceeds_five_sixtyfourths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms neighbor_seeded_advantage_exceeds_five_sixtyfourths

end XmssSecurity.TargetSum.Attack
