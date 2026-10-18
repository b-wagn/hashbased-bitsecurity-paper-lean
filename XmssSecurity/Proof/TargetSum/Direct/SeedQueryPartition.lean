import XmssSecurity.Proof.TargetSum.Direct.SeedGuessingExpected
import XmssSecurity.Proof.Generic.Direct.StructuralQueries
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability
/-! Seed, encoding, and structural queries occupy disjoint parts of the direct-query
budget. The partition holds under any stateful interpretation of the adversary. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum

theorem keygenStructuralTargetInput_of_maySeedHit (secretKey : Generic.SecretKey) (cache : QueryCache HashSpec)
    (input : HashInput) (hseed : Generic.MaySeedHit input) : Generic.keygenStructuralTargetInput secretKey cache input = input := by
  have hchain : Generic.CappedSuffix.keygenChainTargetInput secretKey cache input = input := by
    unfold Generic.CappedSuffix.keygenChainTargetInput
    split
    · rename_i h
      obtain ⟨value, hinput⟩ := h.choose_spec
      exact False.elim (Generic.not_maySeedHit_tweakableHashInput _ _ _ (hinput ▸ hseed))
    · rfl
  have hleaf : Generic.CappedLeaf.keygenLeafTargetInput secretKey cache input = input := by
    unfold Generic.CappedLeaf.keygenLeafTargetInput
    split
    · rename_i h
      obtain ⟨endpoints, hinput⟩ := h.choose_spec
      exact False.elim (Generic.not_maySeedHit_tweakableHashInput _ _ _ (hinput ▸ hseed))
    · rfl
  have hmerkle : Generic.CappedMerkle.keygenMerkleTargetInput secretKey cache input = input := by
    unfold Generic.CappedMerkle.keygenMerkleTargetInput
    split
    · rename_i h
      obtain ⟨left, right, hinput⟩ := h.choose_spec
      exact False.elim (Generic.not_maySeedHit_tweakableHashInput _ _ _ (hinput ▸ hseed))
    · rfl
  rw [Generic.keygenStructuralTargetInput, hchain, hleaf, hmerkle]

namespace Direct

def IsDirectSeedQuery : (OracleWorld + Generic.SigningSpec).Domain → Prop
  | .inl (.inr input) => Generic.MaySeedHit input
  | _ => False

instance : DecidablePred IsDirectSeedQuery := fun input =>
  match input with
  | .inl (.inr input) => inferInstanceAs (Decidable (Generic.MaySeedHit input))
  | .inl (.inl _) | .inr _ => inferInstanceAs (Decidable False)

theorem directSeed_encoding_disjoint (parameter : PublicParameter)
    (input : (OracleWorld + Generic.SigningSpec).Domain) :
    ¬(IsDirectSeedQuery input ∧ Generic.Direct.IsDirectEncodingQuery parameter input) := by
  rcases input with (uniform | input) | request
  · rintro ⟨h, _⟩; exact h.elim
  · rintro ⟨hseed, hencoding⟩
    obtain ⟨leaf, hleaf⟩ := Option.isSome_iff_exists.mp hencoding
    obtain ⟨payload, hinput⟩ := Generic.exists_encodingInput_of_encodingInputLeafIndex?_eq_some parameter input leaf hleaf
    exact Generic.not_maySeedHit_tweakableHashInput _ _ _ (hinput.symm ▸ hseed)
  · rintro ⟨h, _⟩; exact h.elim

theorem directSeed_structural_disjoint (secretKey : Generic.SecretKey) (cache : QueryCache HashSpec)
    (input : (OracleWorld + Generic.SigningSpec).Domain) :
    ¬(IsDirectSeedQuery input ∧ Generic.Direct.IsDirectStructuralQuery secretKey cache input) := by
  rcases input with (uniform | input) | request
  · rintro ⟨h, _⟩; exact h.elim
  · rintro ⟨hseed, hstructural⟩
    exact hstructural (keygenStructuralTargetInput_of_maySeedHit secretKey cache input hseed)
  · rintro ⟨h, _⟩; exact h.elim

theorem directSeed_isDirectHashQuery (input : (OracleWorld + Generic.SigningSpec).Domain)
    (hseed : IsDirectSeedQuery input) : Generic.Direct.IsDirectHashQuery input := by
  rcases input with (uniform | input) | request
  · exact hseed.elim
  · exact Generic.Direct.isDirectHashQuery_hash input
  · exact hseed.elim

theorem expectedDirect_classes_le {α State : Type}
    (impl : QueryImpl (OracleWorld + Generic.SigningSpec) (StateT State ProbComp))
    (secretKey : Generic.SecretKey) (targetCache : QueryCache HashSpec)
    (computation : OracleComp (OracleWorld + Generic.SigningSpec) α) (state : State) :
    expectedSimulatedQueryCount impl (Generic.Direct.IsDirectEncodingQuery secretKey.parameter) computation state +
      expectedSimulatedQueryCount impl (Generic.Direct.IsDirectStructuralQuery secretKey targetCache) computation state +
      expectedSimulatedQueryCount impl IsDirectSeedQuery computation state ≤
        expectedSimulatedQueryCount impl Generic.Direct.IsDirectHashQuery computation state := by
  rw [← expectedSimulatedQueryCount_or_of_disjoint impl _ _
    (Generic.Direct.directEncoding_structural_disjoint secretKey targetCache)]
  have hdisjoint (input : (OracleWorld + Generic.SigningSpec).Domain) :
      ¬((Generic.Direct.IsDirectEncodingQuery secretKey.parameter input ∨ Generic.Direct.IsDirectStructuralQuery secretKey targetCache input) ∧
        IsDirectSeedQuery input) := by
    rintro ⟨h | h, hseed⟩
    · exact directSeed_encoding_disjoint secretKey.parameter input ⟨hseed, h⟩
    · exact directSeed_structural_disjoint secretKey targetCache input ⟨hseed, h⟩
  rw [← expectedSimulatedQueryCount_or_of_disjoint impl _ _ hdisjoint]
  apply expectedSimulatedQueryCount_mono
  intro input h
  rcases h with h | hseed
  · exact Generic.Direct.directEncoding_or_structural_isDirectHashQuery secretKey targetCache input h
  · exact directSeed_isDirectHashQuery input hseed

/-- info: 'XmssSecurity.TargetSum.Direct.expectedDirect_classes_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms expectedDirect_classes_le

end Direct
end XmssSecurity.TargetSum
