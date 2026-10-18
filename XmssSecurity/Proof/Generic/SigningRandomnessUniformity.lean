import VCVio.OracleComp.Constructions.SampleableType
import XmssSecurity.Proof.Generic.HashInputLemmas

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Generic

variable [Code]

noncomputable local instance : SampleableType Randomness :=
  SampleableType.ofFintype Randomness

theorem card_randomness : Fintype.card Randomness = 2 ^ randomnessBits := by
  simp

end XmssSecurity.Generic
