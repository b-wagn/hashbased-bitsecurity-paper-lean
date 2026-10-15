import XmssSecurity.Proof.EUFCMA.Reduction

/-! Regression checks for the distinction between request and signature freshness. -/

namespace XmssSecurity.EUFCMAChecks

open SUFCMA

private def request : SignRequest Bool 2 := ⟨0, false⟩
private def changedSignature : Forgery Bool Bool 2 := ⟨0, false, true⟩
private def changedMessage : Forgery Bool Bool 2 := ⟨0, true, true⟩
private def changedEpoch : Forgery Bool Bool 2 := ⟨1, false, true⟩

-- A new signature on a signed input is strong-fresh, but not standard-fresh.
example : ¬ SigningTranscript.Contains [⟨request, some false⟩] changedSignature := by decide
example : EUFCMA.SigningTranscript.ContainsRequest [⟨request, some false⟩] changedSignature := by decide

-- Even an unsuccessful signing request makes its input ineligible.
example : EUFCMA.SigningTranscript.ContainsRequest [⟨request, none⟩] changedSignature := by decide

-- The signed input includes both the epoch and the message.
example : ¬ EUFCMA.SigningTranscript.ContainsRequest [⟨request, some false⟩] changedMessage := by decide
example : ¬ EUFCMA.SigningTranscript.ContainsRequest [⟨request, some false⟩] changedEpoch := by decide

-- Verification can accept while only the strong game wins, at the same charge.
private def alteredOutcome : EUFCMA.CountedOutcome Bool Bool 2 :=
  ⟨changedSignature, [⟨request, some false⟩], true, 7⟩

example : alteredOutcome.standardResult = (false, 7) := by decide
example : alteredOutcome.strongResult = (true, 7) := by decide

-- A verified new message wins both games.
private def newMessageOutcome : EUFCMA.CountedOutcome Bool Bool 2 :=
  ⟨changedMessage, [⟨request, some false⟩], true, 7⟩

example : newMessageOutcome.standardResult = (true, 7) := by decide
example : newMessageOutcome.strongResult = (true, 7) := by decide

-- Duplicate epochs invalidate the transcript even for a fresh message.
private def invalidOutcome : EUFCMA.CountedOutcome Bool Bool 2 :=
  ⟨changedMessage, [⟨request, some false⟩, ⟨request, none⟩], true, 7⟩

example : invalidOutcome.standardResult = (false, 7) := by decide

end XmssSecurity.EUFCMAChecks
