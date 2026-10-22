import Xmss.Proof.Generic.ConcreteQueryBound

open OracleComp OracleSpec

namespace Xmss.Generic

variable [Code]

theorem Signing.precomputedSignAttempt_queryBound_zero_at_other_encodingInput
    (secretKey : SecretKey) (leafIndex targetLeafIndex : LeafIndex)
    (message : Message) (randomness : Randomness) (targetInput : Message × Randomness)
    (hne : CacheView.encodingInput secretKey.parameter leafIndex
        (message, randomness) ≠
      CacheView.encodingInput secretKey.parameter targetLeafIndex targetInput) :
    (Signing.precomputedSignAttempt secretKey leafIndex message randomness :
      OracleComp HashSpec (Option Signature)).IsQueryBoundP
        (· = CacheView.encodingInput secretKey.parameter targetLeafIndex targetInput) 0 := by
  rw [Signing.precomputedSignAttempt]
  refine OracleComp.isQueryBoundP_bind (m := 0)
    (Hashing.encodingHash_queryBound_zero_at_other_input secretKey.parameter leafIndex
      message randomness
      (CacheView.encodingInput secretKey.parameter targetLeafIndex targetInput) hne) ?_
  intro digest _
  split <;> simp

end Xmss.Generic
