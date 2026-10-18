import XmssSecurity.Proof.Generic.Direct.DecidingClassification

/-! A revealed deciding-chain value is one of the hidden-value events in the existing coupling. -/

open OracleComp OracleSpec

namespace XmssSecurity.Generic.Deciding

variable [Code]

open Concrete

theorem no_returned_of_returnedAt_none (log : QueryLog SigningSpec) (leafIndex : LeafIndex)
    (h : returnedAt log leafIndex = none) :
    ¬ ∃ request signature, SigningTranscript.Returned log request signature ∧
      request.epoch = leafIndex := by
  rintro ⟨request, signature, ⟨entry, hmem, hrequest, hsignature⟩, hepoch⟩
  have hentry := List.findSome?_eq_none_iff.mp h entry hmem
  simp only [hsignature, hrequest, hepoch, ↓reduceIte] at hentry
  cases hentry

/-- The selected hidden value gives a chain event at that same index, with no union over chains. -/
theorem deciding_revealed_chain_event (cache : QueryCache HashSpec) (outcome : GameOutcome)
    (hconsistent : ConcreteOutcomeConsistent cache outcome) (hwin : outcome.won = true)
    (hrevealed : DecidingChainValueRevealed cache outcome) :
    WinningOutcomeBadEventOccurs cache outcome (.chain (outcomeDecidingChain cache outcome)) ∧
      CappedChain.OutcomeChainValueRevealed cache outcome (outcomeDecidingChain cache outcome) := by
  obtain ⟨encoding, hdecode, hbelow, hvalue⟩ := hrevealed
  let chain := decidingChain cache outcome.secretKey outcome.signingLog outcome.forgery encoding
  rw [outcomeDecidingChain_eq cache outcome encoding hdecode]
  have hverified := (outcome.won_eq_true_iff.mp hwin).2.2
  refine ⟨⟨hwin, hverified, ?_⟩, hverified, encoding, hdecode, hvalue⟩
  cases hreturned : returnedAt outcome.signingLog outcome.forgery.epoch with
  | none =>
    refine Or.inr ⟨encoding, (Concrete.CacheView.decodedEncoding_valid hdecode),
      no_returned_of_returnedAt_none _ _ hreturned, hdecode, ?_⟩
    exact hvalue
  | some pair =>
    rcases pair with ⟨request, signature⟩
    obtain ⟨hentry, hepoch⟩ := returned_of_returnedAt _ _ _ _ hreturned
    obtain ⟨signed, hsigned, hsignature⟩ := hconsistent.signing request signature hentry
    have hsigned' : signedEncoding cache outcome.secretKey.parameter outcome.signingLog
        outcome.forgery.epoch = some signed := by
      simpa only [signedEncoding, hreturned, hepoch] using hsigned
    have hlt := hbelow signed hsigned'
    have hforged : CacheView.decodedEncoding cache outcome.secretKey.parameter request.epoch
          (outcome.forgery.message, outcome.forgery.signature.randomness) = some encoding := by
      simpa only [forgedEncoding, hepoch] using hdecode
    refine Or.inl ⟨request, signature, signed, encoding, hsigned, hforged, hentry, hepoch, ?_⟩
    change Wots.IsBackwardWitnessAt _ signed encoding signature.chainValue
      outcome.forgery.signature.chainValue chain
    refine ⟨hlt, ?_⟩
    rw [hepoch]
    change outcome.forgery.signature.chainValue chain = _ at hvalue
    rw [hvalue]
    have hsignedValue : signature.chainValue chain =
        Wots.signChain (CacheView.chainStep cache outcome.secretKey.parameter outcome.forgery.epoch chain)
          (signed chain) (outcome.secretKey.chainStart outcome.forgery.epoch chain) := by
      rw [hsignature, hepoch]
      rfl
    rw [hsignedValue]
    exact Wots.walk_signChain_to_later _ _ _ _ hlt.le

end XmssSecurity.Generic.Deciding
