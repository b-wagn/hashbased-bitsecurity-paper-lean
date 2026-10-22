import Xmss.Proof.Generic.EncodingActionTrace
import VCVio.OracleComp.Constructions.SampleableType

open OracleComp OracleSpec

namespace Xmss.Generic

variable [Code]

inductive EncodingSampleKind where
  | side
  | query
  | sign
deriving DecidableEq

noncomputable def uniformHashOutput : ProbComp Digest :=
  $ᵗ Digest

omit [Code] in
theorem uniformSampleImpl_hash_eq (input : HashInput) :
    (uniformSampleImpl (spec := HashSpec)) input = uniformHashOutput := by
  rfl

omit [Code] in
theorem randomOracle_run_none_eq_uniformHashOutput
    (input : HashInput) (cache : QueryCache HashSpec)
    (hcache : cache input = none) :
    (randomOracle input).run cache =
      (fun output => (output, cache.cacheQuery input output)) <$>
        uniformHashOutput := by
  rw [randomOracle, QueryImpl.withCaching_run_none _ hcache]
  rw [uniformSampleImpl_hash_eq]

end Xmss.Generic
