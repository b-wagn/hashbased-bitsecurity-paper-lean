import XmssSecurity.Proof.Checksum.EncodingOracleSimulation

open OracleComp ENNReal

namespace XmssSecurity.Checksum

set_option maxRecDepth 100000

namespace Checksum

def ValidDigest (digest : Digest) : Prop :=
  ∃ encoding, decodeDigest digest = some encoding

noncomputable instance : DecidablePred ValidDigest :=
  Classical.decPred _

noncomputable def validDigests : Finset Digest :=
  Finset.univ.filter ValidDigest

/-- Every digest decodes. -/
theorem validDigest (digest : Digest) : ValidDigest digest :=
  ⟨encode digest, rfl⟩

theorem validDigests_eq_univ : validDigests = Finset.univ := by
  unfold validDigests
  exact Finset.filter_true_of_mem fun digest _ => validDigest digest

theorem validDigests_card : validDigests.card = 2 ^ digestBits := by
  rw [validDigests_eq_univ, Finset.card_univ]
  simp

theorem validDigests_nonempty : validDigests.Nonempty := by
  rw [validDigests_eq_univ]
  exact Finset.univ_nonempty

theorem validDigests_card_pos : 0 < validDigests.card :=
  Finset.card_pos.mpr validDigests_nonempty

end Checksum

end XmssSecurity.Checksum
