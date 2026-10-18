import XmssSecurity.Proof.TargetSum.EUFCMA.ReplayGame
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Exact transfer of the fresh-message replay attack to deterministic seeded signing. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.EUFCMA
open XmssSecurity.EUFCMA

open Attack Generic.DeterministicSigning

theorem memoAdversary_replay : Generic.Seeded.memoAdversary replayAdversary = replayAdversary := by
  unfold Generic.Seeded.memoAdversary replayAdversary
  congr 1

theorem tableGameRest_replay_noSeed (randomizers : Generic.Seeded.RandomizerOutputs)
    (publicKey : PublicKey) (secretKey : Generic.SecretKey) :
    (Generic.Seeded.gameRest (Generic.Seeded.tableScheme randomizers) replayAdversary
      publicKey secretKey).IsQueryBoundP (Generic.Seeded.hashBad Generic.MaySeedHit) 0 := by
  rw [replay_strong_gameRest, replay_gameRest]
  refine OracleComp.isQueryBoundP_bind (m := 0)
    (Generic.Seeded.liftM_hash_noSeed _ (Generic.Seeded.tableSign_noSeed _ _ _ _)) ?_
  intro answer _
  refine OracleComp.isQueryBoundP_bind (m := 0) (replayAfterSigning_noSeed publicKey answer) ?_
  intro forgery _
  exact Generic.Seeded.liftM_hash_noSeed _ (Generic.Concrete.verify_noSeed _ _ _ _)

theorem tableGameAfterSecrets_replay_noSeed (parameter : PublicParameter)
    (secret : Generic.Seeded.ChainSecrets) (randomizers : Generic.Seeded.RandomizerOutputs) :
    (Generic.Seeded.tableGameAfterSecrets replayAdversary parameter secret randomizers).IsQueryBoundP
      (Generic.Seeded.hashBad Generic.MaySeedHit) 0 := by
  unfold Generic.Seeded.tableGameAfterSecrets
  refine OracleComp.isQueryBoundP_bind (m := 0) (Generic.Seeded.liftM_hash_noSeed _ ?_)
    (fun result _ => tableGameRest_replay_noSeed randomizers _ _)
  rw [withQueryLog, OracleComp.isQueryBoundP_iff_of_map_eq (QueryImpl.fst_map_run_withLogging _ _),
    simulateQ_ofLift_eq_self]
  exact Generic.Concrete.treeNode_noSeed _ _ _ _

theorem replay_seeded_advantage_eq_reference :
    forgeAdvantage Generic.Seeded.scheme replayAdversary = forgeAdvantage Generic.Concrete.scheme replayAdversary := by
  rw [replay_advantage_eq_strong, replay_advantage_eq_strong]
  unfold Generic.forgeAdvantage
  apply probOutput_congr rfl
  calc
    _ = evalDist (Generic.Seeded.independentTableGame replayAdversary) :=
      Generic.Seeded.evalDist_deterministic_eq_table_of_noSeed replayAdversary tableGameAfterSecrets_replay_noSeed
    _ = _ := by
      simpa only [memoAdversary_replay] using Generic.Seeded.evalDist_independentTableGame_memo replayAdversary

theorem replay_seeded_advantage_exceeds_127 :
    ((2 ^ 127 : ℕ) : ℝ≥0∞)⁻¹ < forgeAdvantage Generic.Seeded.scheme replayAdversary := by
  rw [replay_seeded_advantage_eq_reference]
  exact replay_reference_advantage_exceeds_127

/-- info: 'XmssSecurity.TargetSum.EUFCMA.replay_seeded_advantage_exceeds_127' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms replay_seeded_advantage_exceeds_127

end XmssSecurity.TargetSum.EUFCMA
