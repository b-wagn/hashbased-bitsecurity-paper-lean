import XmssSecurity.Proof.Generic.HashInputLemmas
import XmssSecurity.Proof.Generic.StatementLemmas
import XmssSecurity.Proof.Generic.Execution
import XmssSecurity.Proof.Generic.IdealStatement
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling
import VCVio.OracleComp.QueryTracking.Unpredictability

open OracleComp ENNReal

namespace XmssSecurity.Generic.Rom

variable [Code]

/-- A uniform oracle output equals any fixed digest with probability exactly `2^-128`. -/
theorem uniform_eq_probability (target : Digest) :
    Pr[fun output : Digest => output = target | $ᵗ Digest] =
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  rw [probEvent_eq_eq_probOutput, probOutput_uniformSample, card_bitVec]

/-- A uniform oracle output lands in a set of `T.card` digests with probability `T.card / 2^128`. -/
theorem uniform_mem_probability (T : Finset Digest) :
    Pr[fun output : Digest => output ∈ T | $ᵗ Digest] =
      T.card / ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
  classical
  rw [probEvent_uniformSample, Finset.filter_mem_eq_inter, Finset.univ_inter, card_bitVec]

open OracleSpec

noncomputable local instance : IsUniformSpec HashSpec :=
  IsUniformSpec.ofFintypeInhabited _

/-- Each fresh query may select its own target digest without adding an index-set loss. -/
def AdaptiveFreshDigestCollisionWith (initialCache finalCache : QueryCache HashSpec)
    (targetInput : HashInput → HashInput) : Prop :=
  ∃ input output targetOutput,
    finalCache input = some output ∧ initialCache input = none ∧
      initialCache (targetInput input) = some targetOutput ∧
      Concrete.CacheView.digestAt finalCache input =
        Concrete.CacheView.digestAt finalCache (targetInput input)

end XmssSecurity.Generic.Rom
