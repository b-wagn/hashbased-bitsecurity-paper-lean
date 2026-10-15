import XmssSecurity.Proof.EUFCMA.ReplayGame

/-! Exact transfer of the fresh-message replay attack to deterministic seeded signing. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.EUFCMA

open Attack DeterministicSigning

theorem memoize_replayMain (publicKey : PublicKey) :
    memoize (replayMain publicKey) ∅ = replayMain publicKey := by
  unfold replayMain
  rw [memoize_request]
  simp only [QueryCache.empty_apply, memoize_liftWorldToAdversary]

theorem memoAdversary_replay : XmssSecurity.Seeded.memoAdversary replayAdversary = replayAdversary := by
  unfold XmssSecurity.Seeded.memoAdversary replayAdversary
  congr 1

theorem tableGameRest_replay_noSeed (randomizers : XmssSecurity.Seeded.RandomizerOutputs)
    (publicKey : PublicKey) (secretKey : SecretKey) :
    (XmssSecurity.Seeded.gameRest (XmssSecurity.Seeded.tableScheme randomizers) replayAdversary
      publicKey secretKey).IsQueryBoundP (XmssSecurity.Seeded.hashBad MaySeedHit) 0 := by
  rw [replay_strong_gameRest, replay_gameRest]
  refine OracleComp.isQueryBoundP_bind (m := 0)
    (XmssSecurity.Seeded.liftM_hash_noSeed _ (XmssSecurity.Seeded.tableSign_noSeed _ _ _ _)) ?_
  intro answer _
  refine OracleComp.isQueryBoundP_bind (m := 0) (replayAfterSigning_noSeed publicKey answer) ?_
  intro forgery _
  exact XmssSecurity.Seeded.liftM_hash_noSeed _ (Concrete.verify_noSeed _ _ _ _)

theorem tableGameAfterSecrets_replay_noSeed (parameter : PublicParameter)
    (secret : XmssSecurity.Seeded.ChainSecrets) (randomizers : XmssSecurity.Seeded.RandomizerOutputs) :
    (XmssSecurity.Seeded.tableGameAfterSecrets replayAdversary parameter secret randomizers).IsQueryBoundP
      (XmssSecurity.Seeded.hashBad MaySeedHit) 0 := by
  unfold XmssSecurity.Seeded.tableGameAfterSecrets
  refine OracleComp.isQueryBoundP_bind (m := 0) (XmssSecurity.Seeded.liftM_hash_noSeed _ ?_)
    (fun result _ => tableGameRest_replay_noSeed randomizers _ _)
  rw [withQueryLog, OracleComp.isQueryBoundP_iff_of_map_eq (QueryImpl.fst_map_run_withLogging _ _),
    simulateQ_ofLift_eq_self]
  exact Concrete.treeNode_noSeed _ _ _ _

theorem replay_seeded_advantage_eq_reference :
    forgeAdvantage XmssSecurity.Seeded.scheme replayAdversary = forgeAdvantage Concrete.scheme replayAdversary := by
  rw [replay_advantage_eq_strong, replay_advantage_eq_strong]
  unfold XmssSecurity.forgeAdvantage
  apply probOutput_congr rfl
  calc
    _ = evalDist (XmssSecurity.Seeded.independentTableGame replayAdversary) :=
      XmssSecurity.Seeded.evalDist_deterministic_eq_table_of_noSeed replayAdversary tableGameAfterSecrets_replay_noSeed
    _ = _ := by
      simpa only [memoAdversary_replay] using XmssSecurity.Seeded.evalDist_independentTableGame_memo replayAdversary

theorem replay_seeded_advantage_exceeds_127 :
    ((2 ^ 127 : ℕ) : ℝ≥0∞)⁻¹ < forgeAdvantage XmssSecurity.Seeded.scheme replayAdversary := by
  rw [replay_seeded_advantage_eq_reference]
  exact replay_reference_advantage_exceeds_127

/-- info: 'XmssSecurity.EUFCMA.replay_seeded_advantage_exceeds_127' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms replay_seeded_advantage_exceeds_127

end XmssSecurity.EUFCMA
