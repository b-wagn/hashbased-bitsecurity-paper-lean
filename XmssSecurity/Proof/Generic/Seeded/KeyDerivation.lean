import XmssSecurity.Proof.Generic.IdealStatement
import XmssSecurity.Proof.Generic.HashInputLemmas

namespace XmssSecurity.Generic

variable [Code]

private theorem fin_of_ofNat32_eq {n : Nat} {a b : Fin n} (hn : n ≤ 2 ^ 32)
    (h : BitVec.ofNat 32 a.val = BitVec.ofNat 32 b.val) : a = b := by
  apply Fin.ext
  have ha := a.isLt.trans_le hn
  have hb := b.isLt.trans_le hn
  have heq := congrArg BitVec.toNat h
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using heq

theorem keygenDomainFields_injective : Function.Injective keygenDomainFields := by
  intro left right h
  cases left <;> cases right <;>
    simp_all only [keygenDomainFields, tweakFields, TweakFields.mk.injEq, BitVec.reduceEq, false_and,
      true_and, KeygenDomain.chain.injEq]
  obtain ⟨hchain, hleafIndex⟩ := h
  exact ⟨fin_of_ofNat32_eq (by decide) hleafIndex,
    fin_of_ofNat32_eq (Code.numChains_lt.le.trans (by norm_num)) hchain⟩

theorem keygenHashInput_injective {p₁ p₂ : PublicParameter} {d₁ d₂ : KeygenDomain}
    {s₁ s₂ : MasterSeed} (h : keygenHashInput p₁ d₁ s₁ = keygenHashInput p₂ d₂ s₂) :
    p₁ = p₂ ∧ d₁ = d₂ ∧ s₁ = s₂ := by
  unfold keygenHashInput at h
  obtain ⟨hprefix, hseed⟩ := List.append_inj' h (by simp)
  obtain ⟨htweak, hparameter⟩ := List.append_inj' hprefix (by simp)
  exact ⟨bytesLE_injective 16 hparameter,
    keygenDomainFields_injective (fieldBytes_injective htweak), bytesLE_injective 32 hseed⟩

end XmssSecurity.Generic
