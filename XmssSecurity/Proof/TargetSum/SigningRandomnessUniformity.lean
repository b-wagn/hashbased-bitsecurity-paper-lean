import VCVio.OracleComp.Constructions.SampleableType
import XmssSecurity.Proof.TargetSum.HashInputLemmas

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.TargetSum

noncomputable local instance : SampleableType Randomness :=
  SampleableType.ofFintype Randomness

theorem card_randomness : Fintype.card Randomness = 2 ^ randomnessBits := by
  simp

end XmssSecurity.TargetSum
