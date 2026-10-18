import XmssSecurity.Proof.Generic.EncodingOracleSimulation

open OracleComp ENNReal

namespace XmssSecurity.Generic

variable [Code]

set_option maxRecDepth 100000

namespace Code

def ValidDigest (digest : Digest) : Prop :=
  ∃ encoding, decodeDigest digest = some encoding

noncomputable instance : DecidablePred ValidDigest :=
  Classical.decPred _

noncomputable def validDigests : Finset Digest :=
  Finset.univ.filter ValidDigest

theorem validDigests_nonempty : validDigests.Nonempty := by
  obtain ⟨digest, x, h⟩ := exists_decodes
  exact ⟨digest, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, h⟩⟩

theorem validDigests_card_pos : 0 < validDigests.card :=
  Finset.card_pos.mpr validDigests_nonempty

end Code

end XmssSecurity.Generic
