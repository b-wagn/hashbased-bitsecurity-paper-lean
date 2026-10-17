import XmssSecurity.Proof.TargetSum.Direct.SeedGuessingExpected
import XmssSecurity.Proof.TargetSum.Direct.StructuralQueries

/-! Seed, encoding, and structural queries occupy disjoint parts of the direct-query
budget. The partition holds under any stateful interpretation of the adversary. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum

theorem keygenStructuralTargetInput_of_maySeedHit (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (input : HashInput) (hseed : MaySeedHit input) : keygenStructuralTargetInput secretKey cache input = input := by
  have hchain : CappedSuffix.keygenChainTargetInput secretKey cache input = input := by
    unfold CappedSuffix.keygenChainTargetInput
    split
    · rename_i h
      obtain ⟨value, hinput⟩ := h.choose_spec
      exact False.elim (not_maySeedHit_tweakableHashInput _ _ _ (hinput ▸ hseed))
    · rfl
  have hleaf : CappedLeaf.keygenLeafTargetInput secretKey cache input = input := by
    unfold CappedLeaf.keygenLeafTargetInput
    split
    · rename_i h
      obtain ⟨endpoints, hinput⟩ := h.choose_spec
      exact False.elim (not_maySeedHit_tweakableHashInput _ _ _ (hinput ▸ hseed))
    · rfl
  have hmerkle : CappedMerkle.keygenMerkleTargetInput secretKey cache input = input := by
    unfold CappedMerkle.keygenMerkleTargetInput
    split
    · rename_i h
      obtain ⟨left, right, hinput⟩ := h.choose_spec
      exact False.elim (not_maySeedHit_tweakableHashInput _ _ _ (hinput ▸ hseed))
    · rfl
  rw [keygenStructuralTargetInput, hchain, hleaf, hmerkle]

namespace Direct

def IsDirectSeedQuery : (OracleWorld + SigningSpec).Domain → Prop
  | .inl (.inr input) => MaySeedHit input
  | _ => False

instance : DecidablePred IsDirectSeedQuery := fun input =>
  match input with
  | .inl (.inr input) => inferInstanceAs (Decidable (MaySeedHit input))
  | .inl (.inl _) | .inr _ => inferInstanceAs (Decidable False)

theorem directSeed_encoding_disjoint (parameter : PublicParameter)
    (input : (OracleWorld + SigningSpec).Domain) :
    ¬(IsDirectSeedQuery input ∧ IsDirectEncodingQuery parameter input) := by
  rcases input with (uniform | input) | request
  · rintro ⟨h, _⟩; exact h.elim
  · rintro ⟨hseed, hencoding⟩
    obtain ⟨leaf, hleaf⟩ := Option.isSome_iff_exists.mp hencoding
    obtain ⟨payload, hinput⟩ := exists_encodingInput_of_encodingInputLeafIndex?_eq_some parameter input leaf hleaf
    exact not_maySeedHit_tweakableHashInput _ _ _ (hinput.symm ▸ hseed)
  · rintro ⟨h, _⟩; exact h.elim

theorem directSeed_structural_disjoint (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (input : (OracleWorld + SigningSpec).Domain) :
    ¬(IsDirectSeedQuery input ∧ IsDirectStructuralQuery secretKey cache input) := by
  rcases input with (uniform | input) | request
  · rintro ⟨h, _⟩; exact h.elim
  · rintro ⟨hseed, hstructural⟩
    exact hstructural (keygenStructuralTargetInput_of_maySeedHit secretKey cache input hseed)
  · rintro ⟨h, _⟩; exact h.elim

theorem directSeed_isDirectHashQuery (input : (OracleWorld + SigningSpec).Domain)
    (hseed : IsDirectSeedQuery input) : IsDirectHashQuery input := by
  rcases input with (uniform | input) | request
  · exact hseed.elim
  · exact isDirectHashQuery_hash input
  · exact hseed.elim

theorem expectedDirect_classes_le {α State : Type}
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT State ProbComp))
    (secretKey : SecretKey) (targetCache : QueryCache HashSpec)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : State) :
    expectedSimulatedQueryCount impl (IsDirectEncodingQuery secretKey.parameter) computation state +
      expectedSimulatedQueryCount impl (IsDirectStructuralQuery secretKey targetCache) computation state +
      expectedSimulatedQueryCount impl IsDirectSeedQuery computation state ≤
        expectedSimulatedQueryCount impl IsDirectHashQuery computation state := by
  rw [← expectedSimulatedQueryCount_or_of_disjoint impl _ _
    (directEncoding_structural_disjoint secretKey targetCache)]
  have hdisjoint (input : (OracleWorld + SigningSpec).Domain) :
      ¬((IsDirectEncodingQuery secretKey.parameter input ∨ IsDirectStructuralQuery secretKey targetCache input) ∧
        IsDirectSeedQuery input) := by
    rintro ⟨h | h, hseed⟩
    · exact directSeed_encoding_disjoint secretKey.parameter input ⟨hseed, h⟩
    · exact directSeed_structural_disjoint secretKey targetCache input ⟨hseed, h⟩
  rw [← expectedSimulatedQueryCount_or_of_disjoint impl _ _ hdisjoint]
  apply expectedSimulatedQueryCount_mono
  intro input h
  rcases h with h | hseed
  · exact directEncoding_or_structural_isDirectHashQuery secretKey targetCache input h
  · exact directSeed_isDirectHashQuery input hseed

/-- info: 'XmssSecurity.TargetSum.Direct.expectedDirect_classes_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms expectedDirect_classes_le

end Direct
end XmssSecurity.TargetSum
