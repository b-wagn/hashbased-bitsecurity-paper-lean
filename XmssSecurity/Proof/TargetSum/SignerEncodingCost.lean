import XmssSecurity.Proof.TargetSum.ExpectedCountedQueries
import XmssSecurity.Proof.TargetSum.EncodingAcceptanceBudget
import XmssSecurity.Proof.Generic.Direct.SeedGuessing
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability
/-! Every seeded signing attempt pairs one derivation hash with one encoding hash. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.TargetSum

theorem deriveRandomizer_lift_hash_eq_world
    (parameter : PublicParameter) (seed : MasterSeed) (leafIndex : LeafIndex)
    (message : Message) (trial : BitVec 32) :
    (liftM (Generic.deriveRandomizer parameter seed leafIndex message trial : OracleComp HashSpec Randomness) :
      OracleComp OracleWorld Randomness) = Generic.deriveRandomizer parameter seed leafIndex message trial := by
  simp only [Generic.deriveRandomizer, Generic.Concrete.oracleHash, liftM_bind, liftM_pure]
  rfl

theorem Concrete.precomputedSignAttempt_lift_hash_eq_world
    (secretKey : Generic.SecretKey) (leafIndex : LeafIndex) (message : Message) (randomness : Randomness) :
    (liftM (Generic.Concrete.precomputedSignAttempt secretKey leafIndex message randomness :
      OracleComp HashSpec (Option Generic.Signature)) : OracleComp OracleWorld (Option Generic.Signature)) =
      Generic.Concrete.precomputedSignAttempt secretKey leafIndex message randomness := by
  have hencoding : (liftM (Generic.Concrete.encodingHash secretKey.parameter leafIndex message randomness :
      OracleComp HashSpec Digest) : OracleComp OracleWorld Digest) =
      Generic.Concrete.encodingHash secretKey.parameter leafIndex message randomness := by
    simp only [Generic.Concrete.encodingHash, Generic.Concrete.tweakableHash, Generic.Concrete.oracleHash, liftM_bind, liftM_pure]
    rfl
  rw [Generic.Concrete.precomputedSignAttempt, liftM_bind, hencoding, Generic.Concrete.precomputedSignAttempt]
  apply bind_congr
  intro digest
  cases Generic.Code.decodeDigest digest <;> simp only [liftM_pure]

theorem Seeded.signFrom_lift_hash_eq_world
    (secretKey : Generic.Seeded.SecretKey) (leafIndex : LeafIndex) (message : Message) (attempts trial : ℕ) :
    (liftM (Generic.Seeded.signFrom secretKey leafIndex message attempts trial :
      OracleComp HashSpec (Option Generic.Signature)) : OracleComp OracleWorld (Option Generic.Signature)) =
      Generic.Seeded.signFrom secretKey leafIndex message attempts trial := by
  induction attempts generalizing trial with
  | zero => simp [Generic.Seeded.signFrom]
  | succ attempts ih =>
      simp only [Generic.Seeded.signFrom, liftM_bind, deriveRandomizer_lift_hash_eq_world,
        Concrete.precomputedSignAttempt_lift_hash_eq_world]
      apply bind_congr
      intro randomness
      apply bind_congr
      intro answer
      cases answer <;> simp only [ih, liftM_pure]

end XmssSecurity.TargetSum
