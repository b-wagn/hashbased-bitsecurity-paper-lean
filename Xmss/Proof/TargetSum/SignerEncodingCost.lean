import Xmss.Proof.TargetSum.ExpectedCountedQueries
import Xmss.Proof.TargetSum.EncodingAcceptanceBudget
import Xmss.Proof.Generic.Direct.SeedGuessing
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability
/-! Every seeded signing attempt pairs one derivation hash with one encoding hash. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

open Xmss.Generic

namespace Xmss.TargetSum

theorem deriveRandomizer_lift_hash_eq_world
    (parameter : PublicParameter) (seed : MasterSeed) (leafIndex : LeafIndex)
    (message : Message) (trial : BitVec 32) :
    (liftM (Generic.deriveRandomizer parameter seed leafIndex message trial : OracleComp HashSpec Randomness) :
      OracleComp OracleWorld Randomness) = Generic.deriveRandomizer parameter seed leafIndex message trial := by
  simp only [Generic.deriveRandomizer, Generic.Hashing.oracleHash]
  rfl

theorem Signing.precomputedSignAttempt_lift_hash_eq_world
    (secretKey : Generic.SecretKey) (leafIndex : LeafIndex) (message : Message) (randomness : Randomness) :
    (liftM (Generic.Signing.precomputedSignAttempt secretKey leafIndex message randomness :
      OracleComp HashSpec (Option Generic.Signature)) : OracleComp OracleWorld (Option Generic.Signature)) =
      Generic.Signing.precomputedSignAttempt secretKey leafIndex message randomness := by
  have hencoding : (liftM (Generic.Hashing.encodingHash secretKey.parameter leafIndex message randomness :
      OracleComp HashSpec Digest) : OracleComp OracleWorld Digest) =
      Generic.Hashing.encodingHash secretKey.parameter leafIndex message randomness := by
    simp only [Generic.Hashing.encodingHash, Generic.Hashing.tweakableHash, Generic.Hashing.oracleHash]
    rfl
  rw [Generic.Signing.precomputedSignAttempt, liftM_bind, hencoding, Generic.Signing.precomputedSignAttempt]
  apply bind_congr
  intro digest
  cases Code.decodeDigest digest <;> simp only [liftM_pure]

theorem Seeded.signFrom_lift_hash_eq_world
    (secretKey : Generic.Seeded.SecretKey) (leafIndex : LeafIndex) (message : Message) (attempts trial : ℕ) :
    (liftM (Generic.Seeded.signFrom secretKey leafIndex message attempts trial :
      OracleComp HashSpec (Option Generic.Signature)) : OracleComp OracleWorld (Option Generic.Signature)) =
      Generic.Seeded.signFrom secretKey leafIndex message attempts trial := by
  induction attempts generalizing trial with
  | zero => simp [Generic.Seeded.signFrom]
  | succ attempts ih =>
      simp only [Generic.Seeded.signFrom, liftM_bind, deriveRandomizer_lift_hash_eq_world,
        Signing.precomputedSignAttempt_lift_hash_eq_world]
      apply bind_congr
      intro randomness
      apply bind_congr
      intro answer
      cases answer <;> simp only [ih, liftM_pure]

end Xmss.TargetSum
