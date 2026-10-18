import XmssSecurity.Proof.TargetSum.EncodingAcceptanceBudget
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Sample the final hash output conditioned on an accepted encoding. Any event
that rejects invalid encodings factors by the exact ordinary acceptance probability. -/

open OracleComp OracleSpec ENNReal
open scoped Classical

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.TargetSum.TargetSum

abbrev AcceptedHashOutput := {output : HashOutput // Generic.Code.ValidDigest (Generic.truncateHash output)}

noncomputable instance acceptedHashOutputFintype : Fintype AcceptedHashOutput := by
  infer_instance

instance acceptedHashOutputNonempty : Nonempty AcceptedHashOutput := by
  have hpositive : 0 < Pr[fun output : HashOutput => Generic.Code.ValidDigest (Generic.truncateHash output) | $ᵗ HashOutput] := by
    rw [probEvent_validDigest_uniformHashOutput]
    exact acceptanceProbability_pos
  obtain ⟨output, _hsupport, hvalid⟩ := probEvent_pos_iff.mp hpositive
  exact ⟨⟨output, hvalid⟩⟩

noncomputable instance acceptedHashOutputSampleable : SampleableType AcceptedHashOutput :=
  SampleableType.ofFintype AcceptedHashOutput

noncomputable def acceptedHashEncoding (output : AcceptedHashOutput) : Encoding :=
  Classical.choose output.2

theorem acceptedHashEncoding_decode (output : AcceptedHashOutput) :
    Generic.Code.decodeDigest (Generic.truncateHash output.1) = some (acceptedHashEncoding output) :=
  Classical.choose_spec output.2

end XmssSecurity.TargetSum.TargetSum
