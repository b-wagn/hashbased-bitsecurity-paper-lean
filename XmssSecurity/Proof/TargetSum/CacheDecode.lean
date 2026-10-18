import XmssSecurity.Proof.Generic.StatementLemmas
import XmssSecurity.Proof.TargetSum.Code

/-! With the target-sum code an uncached encoding input reads the digest `0`, which does not
decode, so a decoding digest read from the cache witnesses the encoding query. -/

open OracleComp OracleSpec

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum

open Concrete.CacheView

theorem decodedEncoding_of_decodeDigest {cache : QueryCache HashSpec}
    {parameter : PublicParameter} {leafIndex : LeafIndex} {input : Message × Randomness}
    {encoding : Generic.Encoding}
    (h : Code.decodeDigest (encodingHash cache parameter leafIndex input) = some encoding) :
    decodedEncoding cache parameter leafIndex input = some encoding := by
  unfold encodingHash digestAt at h
  unfold decodedEncoding
  cases hcache : cache (encodingInput parameter leafIndex input) with
  | none =>
      rw [hcache] at h
      have hzero : Code.decodeDigest (0 : Digest) = none :=
        TargetSum.decodeDigest_zero_eq_none
      rw [hzero] at h
      cases h
  | some output =>
      rw [hcache] at h
      exact h

theorem encodingInput_cached_of_decode_some
    (cache : QueryCache HashSpec) (parameter : PublicParameter) (leafIndex : LeafIndex)
    (message : Message) (randomness : Randomness) (encoding : Generic.Encoding)
    (hdecode : Code.decodeDigest
      (encodingHash cache parameter leafIndex (message, randomness)) = some encoding) :
    ∃ output, cache (encodingInput parameter leafIndex (message, randomness)) = some output :=
  Concrete.CacheView.encodingInput_cached_of_decode_some cache parameter leafIndex message
    randomness encoding (decodedEncoding_of_decodeDigest hdecode)

end XmssSecurity.TargetSum
