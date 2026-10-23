import Xmss.Proof.TargetSum.Direct.SourceSignerQueries
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! A forged encoding cached on every execution requires at least one expected
encoding query, paid by direct queries or the signer. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum

theorem one_le_cachedEncodingInputCount_of_cached (parameter : PublicParameter)
    (cache : QueryCache HashSpec) (leafIndex : LeafIndex) (payload : Message × Randomness)
    (hcached : cache (CacheView.encodingInput parameter leafIndex payload) ≠ none) :
    1 ≤ cachedEncodingInputCount cache parameter := by
  cases hentry : cache (CacheView.encodingInput parameter leafIndex payload) with
  | none => exact (hcached hentry).elim
  | some output =>
      let entry : (input : HashSpec.Domain) × HashSpec.Range input :=
        ⟨CacheView.encodingInput parameter leafIndex payload, output⟩
      have hsubset : ({entry} : Set ((input : HashSpec.Domain) × HashSpec.Range input)) ⊆
          cachedEncodingInputSet cache parameter := by
        intro candidate hcand
        simp only [Set.mem_singleton_iff] at hcand
        subst candidate
        exact ⟨hentry, by simp [entry]⟩
      simpa only [cachedEncodingInputCount, Set.encard_singleton, ENat.toENNReal_one] using
        ENat.toENNReal_mono (Set.encard_mono hsubset)

namespace Direct

end Direct
end Xmss.TargetSum
