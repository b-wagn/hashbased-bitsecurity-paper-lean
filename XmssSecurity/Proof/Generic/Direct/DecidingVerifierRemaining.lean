import XmssSecurity.Proof.Generic.Direct.DecidingVerifierCount
import XmssSecurity.Proof.Generic.Direct.ForgedEncodingQuery

/-! The path count retains the digit fixed by the cached encoding hash. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.Generic.Deciding

variable [Code]

open Direct

theorem expectedSimulatedQueryCount_verify_remaining_le (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (publicKey : PublicKey)
    (hparam : publicKey.parameter = secretKey.parameter) (leafIndex : LeafIndex)
    (message : Message) (signature : Signature) (chain : ChainIndex)
    (initialCache : QueryCache HashSpec) (encoding : Encoding)
    (hdecode : Concrete.CacheView.decodedEncoding initialCache publicKey.parameter leafIndex
      (message, signature.randomness) = some encoding) :
    expectedSimulatedQueryCount romImpl
      (Rom.IsRelevantHashQuery fun input =>
        decidingTargetInput secretKey cache leafIndex chain input ≠ input)
      (Concrete.scheme.verify publicKey leafIndex message signature) initialCache ≤
      (decidingQueryBound - (encoding chain).val : ℕ) := by
  classical
  let input := Concrete.CacheView.encodingInput publicKey.parameter leafIndex
    (message, signature.randomness)
  let p := Rom.IsRelevantHashQuery fun input =>
    decidingTargetInput secretKey cache leafIndex chain input ≠ input
  obtain ⟨output, hcached⟩ := Concrete.CacheView.encodingInput_cached_of_decode_some
    initialCache publicKey.parameter leafIndex message signature.randomness encoding hdecode
  have hdigest : Code.decodeDigest output = some encoding := by
    simpa [Concrete.CacheView.decodedEncoding, Concrete.CacheView.encodingHash,
      Concrete.CacheView.digestAt, hcached] using hdecode
  have hquery : (romImpl (.inr input)).run initialCache = pure (output, initialCache) := by
    change (randomOracle input).run initialCache = _
    exact QueryImpl.withCaching_run_some _ hcached
  have hnot : ¬ p (.inr input) := by
    intro h
    have hd := isDecidingInput_of_decidingTargetInput_ne secretKey cache leafIndex chain input h
    rw [← hparam] at hd
    exact not_isDecidingInput_encoding publicKey.parameter leafIndex chain leafIndex _ hd
  change expectedSimulatedQueryCount romImpl p
    (liftComp (Concrete.verify publicKey leafIndex message signature :
      OracleComp HashSpec Bool) OracleWorld) initialCache ≤ _
  rw [concrete_verify_eq_query_bind, liftComp_bind]
  change expectedSimulatedQueryCount romImpl p
    (liftM (OracleWorld.query (.inr input)) >>= fun output =>
      liftComp (verifyAfterDigest publicKey leafIndex signature output) OracleWorld)
        initialCache ≤ _
  rw [expectedSimulatedQueryCount_query_bind, if_neg hnot, zero_add, hquery,
    tsum_probOutput_pure_mul]
  unfold verifyAfterDigest
  rw [hdigest]
  apply expectedSimulatedQueryCount_le_of_isQueryBoundP
  apply OracleComp.IsQueryBoundP.liftComp_subSpec
    (p := fun input => decidingTargetInput secretKey cache leafIndex chain input ≠ input)
    (fun _ => Iff.rfl)
  exact verify_after_decode_isQueryBoundP_deciding_remaining secretKey.parameter leafIndex chain
    _ (fun input h => isDecidingInput_of_decidingTargetInput_ne secretKey cache leafIndex chain
      input h) publicKey hparam encoding signature

end XmssSecurity.Generic.Deciding
