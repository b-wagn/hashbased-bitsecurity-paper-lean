import VCVio.OracleComp.Constructions.SampleableType
import Xmss.Proof.Generic.HashInputLemmas

open OracleComp OracleSpec ENNReal

namespace Xmss.Generic

variable [Code]

omit [Code] in
theorem card_randomness : Fintype.card Randomness = 2 ^ digestBits := by
  simp

end Xmss.Generic
