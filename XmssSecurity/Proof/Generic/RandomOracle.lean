import XmssSecurity.Proof.Generic.IdealStatement
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling
import VCVio.OracleComp.QueryTracking.Unpredictability

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Generic.Rom

variable [Code]

noncomputable local instance : IsUniformSpec HashSpec :=
  IsUniformSpec.ofFintypeInhabited _

theorem card_digest : Fintype.card Digest = 2 ^ digestBits := by
  simp

end XmssSecurity.Generic.Rom
