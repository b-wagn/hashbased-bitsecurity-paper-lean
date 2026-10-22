import Xmss.Proof.Generic.Direct.SeedGuessing
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability
/-! Honest operations of the independent reference scheme never query seed-derivation domains. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum.Seeded

variable [Code]

omit [Code] in
theorem liftM_probComp_noSeed {α : Type} (computation : ProbComp α) :
    (liftM computation : OracleComp OracleWorld α).IsQueryBoundP (Seeded.hashBad MaySeedHit) 0 :=
  OracleComp.IsQueryBoundP.liftComp_subSpec
    (p := fun _ : unifSpec.Domain => False) (fun _ => Iff.rfl)
    (OracleComp.isQueryBoundP_false computation 0)

theorem referenceKeygen_noSeed :
    precomputedScheme.keygen.IsQueryBoundP (Seeded.hashBad MaySeedHit) 0 := by
  change Keygen.precomputedKeygen.IsQueryBoundP _ 0
  rw [Keygen.precomputedKeygen]
  refine OracleComp.isQueryBoundP_bind (n := 0) (m := 0) (liftM_probComp_noSeed _) ?_
  intro parameter _
  refine OracleComp.isQueryBoundP_bind (n := 0) (m := 0) (liftM_probComp_noSeed _) ?_
  intro secret _
  refine OracleComp.isQueryBoundP_bind (n := 0) (m := 0) (Seeded.liftM_hash_noSeed _ ?_) ?_
  · rw [withQueryLog, OracleComp.isQueryBoundP_iff_of_map_eq (QueryImpl.fst_map_run_withLogging _ _),
      simulateQ_ofLift_eq_self]
    exact Merkle.treeNode_noSeed _ _ _ _
  · intro result _
    exact OracleComp.isQueryBoundP_pure _ _ _

theorem precomputedSignBoundedAttempts_noSeed (attempts : Nat) (secretKey : Generic.SecretKey)
    (leafIndex : LeafIndex) (message : Message) :
    (Signing.precomputedSignBoundedAttempts attempts secretKey leafIndex message).IsQueryBoundP
      (Seeded.hashBad MaySeedHit) 0 := by
  induction attempts with
  | zero => exact OracleComp.isQueryBoundP_pure _ _ _
  | succ attempts ih =>
      rw [Signing.precomputedSignBoundedAttempts]
      refine OracleComp.isQueryBoundP_bind (n := 0) (m := 0) (liftM_probComp_noSeed _) ?_
      intro randomness _
      refine OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
        (Seeded.liftM_hash_noSeed _ (Signing.precomputedSignAttempt_noSeed _ _ _ _)) ?_
      intro result _
      cases result with
      | none => exact ih
      | some signature => exact OracleComp.isQueryBoundP_pure _ _ _

theorem referenceSign_noSeed (secretKey : Generic.SecretKey)
    (leafIndex : LeafIndex) (message : Message) :
    (precomputedScheme.sign secretKey leafIndex message).IsQueryBoundP (Seeded.hashBad MaySeedHit) 0 := by
  change (Signing.precomputedCappedSign secretKey leafIndex message).IsQueryBoundP _ 0
  rw [Signing.precomputedCappedSign]
  exact precomputedSignBoundedAttempts_noSeed _ _ _ _

theorem referenceVerify_noSeed (publicKey : PublicKey) (leafIndex : LeafIndex)
    (message : Message) (signature : Generic.Signature) :
    (precomputedScheme.verify publicKey leafIndex message signature).IsQueryBoundP (Seeded.hashBad MaySeedHit) 0 :=
  Seeded.liftM_hash_noSeed _ (Verify.verify_noSeed _ _ _ _)

/-- info: 'Xmss.TargetSum.Seeded.referenceKeygen_noSeed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms referenceKeygen_noSeed

/-- info: 'Xmss.TargetSum.Seeded.referenceSign_noSeed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms referenceSign_noSeed

end Xmss.TargetSum.Seeded
