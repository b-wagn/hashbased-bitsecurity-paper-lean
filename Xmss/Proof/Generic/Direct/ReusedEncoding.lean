import Xmss.Proof.Generic.Direct.DecidingClassification

/-! A forgery that reuses the sole signed encoding input has only a structural bad event.
In particular, neither an encoding collision nor a hidden deciding value needs to be charged.
-/

open OracleComp OracleSpec

namespace Xmss.Generic.Deciding

variable [Code]

open Hashing Wots Merkle Verify Keygen Signing

/-- Every signature returned at the forgery's epoch used its encoding input. -/
def ReusesEncodingInput (log : QueryLog SigningSpec) (forgery : Forgery) : Prop :=
  ∀ request signature, SigningTranscript.Returned log request signature →
    request.epoch = forgery.epoch →
      (request.message, signature.randomness) =
        (forgery.message, forgery.signature.randomness)

theorem reusesEncodingInput_singleton (request : SignRequest) (signature : Signature)
    (forgery : Forgery)
    (hinput : (request.message, signature.randomness) =
      (forgery.message, forgery.signature.randomness)) :
    ReusesEncodingInput [⟨request, some signature⟩] forgery := by
  intro other answer hreturned _
  obtain ⟨entry, hmem, hrequest, hanswer⟩ := hreturned
  have hentry : entry = ⟨request, some signature⟩ := by simpa using hmem
  subst entry
  simp only at hrequest hanswer
  cases hrequest
  cases hanswer
  exact hinput

theorem not_encoding_event_of_reuses (cache : QueryCache HashSpec) (outcome : GameOutcome)
    (hreuses : ReusesEncodingInput outcome.signingLog outcome.forgery) :
    ¬ OutcomeBadEventOccurs cache outcome .encoding := by
  rintro ⟨_, hevent | hevent⟩
  · obtain ⟨request, signature, signed, forged, hsigned, hforged, hreturned, hepoch,
      hcollision⟩ := hevent
    exact hcollision.1 (hreuses request signature hreturned hepoch)
  · obtain ⟨encoding, hvalid, hfresh, hdecode, hcollision⟩ := hevent
    exact hcollision

/-- When the signed and forged encoding inputs agree, their decoded encodings agree. -/
theorem signedEncoding_eq_forged_of_reuses (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (log : QueryLog SigningSpec) (forgery : Forgery)
    (hreuses : ReusesEncodingInput log forgery)
    (hreturned : returnedAt log forgery.epoch ≠ none) :
    signedEncoding cache parameter log forgery.epoch = forgedEncoding cache parameter forgery := by
  obtain ⟨⟨request, signature⟩, hpair⟩ := Option.ne_none_iff_exists.mp hreturned
  have hpair := hpair.symm
  obtain ⟨hentry, hepoch⟩ := returned_of_returnedAt _ _ _ _ hpair
  simp only [signedEncoding, hpair, forgedEncoding]
  rw [hreuses request signature hentry hepoch]

theorem not_deciding_revealed_of_reuses (cache : QueryCache HashSpec) (outcome : GameOutcome)
    (hreuses : ReusesEncodingInput outcome.signingLog outcome.forgery)
    (hreturned : returnedAt outcome.signingLog outcome.forgery.epoch ≠ none) :
    ¬ DecidingChainValueRevealed cache outcome := by
  rintro ⟨encoding, hdecode, hbelow, _⟩
  have hsigned := signedEncoding_eq_forged_of_reuses cache outcome.secretKey.parameter
    outcome.signingLog outcome.forgery hreuses hreturned
  rw [hdecode] at hsigned
  exact (lt_irrefl _) (hbelow encoding hsigned)

/-- Reusing a returned encoding input leaves only the deciding structural collision. -/
theorem winning_reused_encoding_structural (cache : QueryCache HashSpec) (outcome : GameOutcome)
    (hconsistent : ConcreteOutcomeConsistent cache outcome) (hwin : outcome.won = true)
    (hreuses : ReusesEncodingInput outcome.signingLog outcome.forgery)
    (hreturned : returnedAt outcome.signingLog outcome.forgery.epoch ≠ none) :
    ∃ encoding, forgedEncoding cache outcome.secretKey.parameter outcome.forgery = some encoding ∧
      DecidingStructuralCollision cache outcome encoding := by
  rcases winning_outcome_deciding_classification cache outcome hconsistent hwin with
    hencoding | hrevealed | hstructural
  · exact (not_encoding_event_of_reuses cache outcome hreuses hencoding).elim
  · exact (not_deciding_revealed_of_reuses cache outcome hreuses hreturned hrevealed).elim
  · exact hstructural

end Xmss.Generic.Deciding
