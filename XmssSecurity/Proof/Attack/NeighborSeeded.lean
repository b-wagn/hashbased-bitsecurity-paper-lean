import XmssSecurity.Proof.Attack.NeighborGame
import XmssSecurity.Proof.Direct.SeedGuessingZero

/-! Exact transfer of the neighboring-signature attack to deterministic seeded signing. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.Attack

open DeterministicSigning

theorem memoize_liftWorldToAdversary {α : Type} (computation : OracleComp OracleWorld α)
    (cache : QueryCache SigningSpec) :
    memoize (liftWorldToAdversary computation) cache = liftWorldToAdversary computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [liftWorldToAdversary, memoize_pure]
  | query_bind input next ih =>
      simp only [liftWorldToAdversary, simulateQ_bind, simulateQ_spec_query] at ih ⊢
      rw [memoize_base]
      exact bind_congr ih

theorem memoize_neighborMain (publicKey : PublicKey) :
    memoize (neighborMain publicKey) ∅ = neighborMain publicKey := by
  unfold neighborMain
  rw [memoize_request]
  simp only [QueryCache.empty_apply, bind_pure_comp, memoize_map, memoize_liftWorldToAdversary]

theorem memoAdversary_neighbor : Seeded.memoAdversary neighborAdversary = neighborAdversary := by
  unfold Seeded.memoAdversary neighborAdversary
  congr 1
  funext publicKey
  exact memoize_neighborMain publicKey

theorem tableGameRest_neighbor_noSeed (randomizers : Seeded.RandomizerOutputs)
    (publicKey : PublicKey) (secretKey : SecretKey) :
    (Seeded.gameRest (Seeded.tableScheme randomizers) neighborAdversary publicKey secretKey).IsQueryBoundP
      (Seeded.hashBad MaySeedHit) 0 := by
  rw [neighbor_gameRest]
  refine OracleComp.isQueryBoundP_bind (m := 0)
    (Seeded.liftM_hash_noSeed _ (Seeded.tableSign_noSeed _ _ _ _)) ?_
  intro answer _
  refine OracleComp.isQueryBoundP_bind (m := 0) (neighborAfterSigning_noSeed publicKey answer) ?_
  intro signature _
  exact Seeded.liftM_hash_noSeed _ (Concrete.verify_noSeed _ _ _ _)

theorem tableGameAfterSecrets_neighbor_noSeed (parameter : PublicParameter)
    (secret : Seeded.ChainSecrets) (randomizers : Seeded.RandomizerOutputs) :
    (Seeded.tableGameAfterSecrets neighborAdversary parameter secret randomizers).IsQueryBoundP
      (Seeded.hashBad MaySeedHit) 0 := by
  unfold Seeded.tableGameAfterSecrets
  refine OracleComp.isQueryBoundP_bind (m := 0) (Seeded.liftM_hash_noSeed _ ?_)
    (fun result _ => tableGameRest_neighbor_noSeed randomizers _ _)
  rw [withQueryLog, OracleComp.isQueryBoundP_iff_of_map_eq (QueryImpl.fst_map_run_withLogging _ _),
    simulateQ_ofLift_eq_self]
  exact Concrete.treeNode_noSeed _ _ _ _

theorem neighbor_seeded_advantage_eq_reference :
    forgeAdvantage Seeded.scheme neighborAdversary = forgeAdvantage Concrete.scheme neighborAdversary := by
  unfold forgeAdvantage
  apply probOutput_congr rfl
  calc
    _ = evalDist (Seeded.independentTableGame neighborAdversary) :=
      Seeded.evalDist_deterministic_eq_table_of_noSeed neighborAdversary tableGameAfterSecrets_neighbor_noSeed
    _ = _ := by
      simpa only [memoAdversary_neighbor] using Seeded.evalDist_independentTableGame_memo neighborAdversary

theorem neighbor_seeded_advantage_exceeds_five_sixtyfourths :
    5 / 64 < forgeAdvantage Seeded.scheme neighborAdversary := by
  rw [neighbor_seeded_advantage_eq_reference]
  exact neighbor_reference_advantage_exceeds_five_sixtyfourths

/-- info: 'XmssSecurity.Attack.neighbor_seeded_advantage_exceeds_five_sixtyfourths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms neighbor_seeded_advantage_exceeds_five_sixtyfourths

end XmssSecurity.Attack
