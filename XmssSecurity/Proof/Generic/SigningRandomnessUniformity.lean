import VCVio.OracleComp.Constructions.SampleableType
import XmssSecurity.Proof.Generic.HashInputLemmas

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Generic

variable [Code]

theorem card_randomness : Fintype.card Randomness = 2 ^ digestBits := by
  simp

end XmssSecurity.Generic
