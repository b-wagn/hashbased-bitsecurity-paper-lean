import XmssSecurity.Proof.TargetSum.ExpectedCountedQueries
import XmssSecurity.Proof.TargetSum.EncodingAcceptanceBudget
import XmssSecurity.Proof.TargetSum.Direct.SeedGuessing

/-! Every seeded signing attempt pairs one derivation hash with one encoding hash. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.TargetSum

theorem deriveRandomizer_lift_hash_eq_world
    (parameter : PublicParameter) (seed : MasterSeed) (leafIndex : LeafIndex)
    (message : Message) (trial : BitVec 32) :
    (liftM (deriveRandomizer parameter seed leafIndex message trial : OracleComp HashSpec Randomness) :
      OracleComp OracleWorld Randomness) = deriveRandomizer parameter seed leafIndex message trial := by
  simp only [deriveRandomizer, Concrete.oracleHash, liftM_bind, liftM_pure]
  rfl

theorem Concrete.precomputedSignAttempt_lift_hash_eq_world
    (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message) (randomness : Randomness) :
    (liftM (precomputedSignAttempt secretKey leafIndex message randomness :
      OracleComp HashSpec (Option Signature)) : OracleComp OracleWorld (Option Signature)) =
      precomputedSignAttempt secretKey leafIndex message randomness := by
  have hencoding : (liftM (encodingHash secretKey.parameter leafIndex message randomness :
      OracleComp HashSpec Digest) : OracleComp OracleWorld Digest) =
      encodingHash secretKey.parameter leafIndex message randomness := by
    simp only [encodingHash, tweakableHash, oracleHash, liftM_bind, liftM_pure]
    rfl
  rw [precomputedSignAttempt, liftM_bind, hencoding, precomputedSignAttempt]
  apply bind_congr
  intro digest
  cases TargetSum.decodeDigest digest <;> simp only [liftM_pure]

theorem Seeded.signFrom_lift_hash_eq_world
    (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message) (attempts trial : ℕ) :
    (liftM (signFrom secretKey leafIndex message attempts trial :
      OracleComp HashSpec (Option Signature)) : OracleComp OracleWorld (Option Signature)) =
      signFrom secretKey leafIndex message attempts trial := by
  induction attempts generalizing trial with
  | zero => simp [signFrom]
  | succ attempts ih =>
      simp only [signFrom, liftM_bind, deriveRandomizer_lift_hash_eq_world,
        Concrete.precomputedSignAttempt_lift_hash_eq_world]
      apply bind_congr
      intro randomness
      apply bind_congr
      intro answer
      cases answer <;> simp only [ih, liftM_pure]

end XmssSecurity.TargetSum
