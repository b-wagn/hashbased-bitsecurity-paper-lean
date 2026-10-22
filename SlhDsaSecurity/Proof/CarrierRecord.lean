import SlhDsaSecurity.Proof.CarrierPhaseRecord
import SlhDsaSecurity.Proof.CarrierTailRecordings

/-!
# Every target-recorded input of the carrier tail is a query the record holds

`LateProvenance.hrecord` at the tail the obligations are moving to. The shape of the argument is
the one that file already has — the game splits at its three sequencing points and each branch
asks its question of the object that can answer it — and only the signer's two branches differ.

**Both differ by reading the flag instead of the bytes.** The randomiser probe is excluded by
`AnswerCarrier.not_carrierRightKeep_randomizerInput`, which compares against the frame in
flight rather than against a syntactic class; the digest probe by
`HandlerCarrier.FilesLeft` holding at the carrier it was filed at, which is what the sub-run's
framing and its queries were carried out for.

This is the input to the bracketed containment, not the plug for the shared assembly's socket:
`LateProbes.probes_le_recordMessageClass` is what takes it, and the socket a layer up takes the
ordering charge's conclusion instead.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.CarrierRecord

open Security BracketedRun CarrierFiles CarrierRecordings CarrierSignRecord CarrierPhaseRecord
  CarriedWitness CarrierTail RecordedQueries AnswerCarrier

set_option maxHeartbeats 1000000 in
/-- **The signer's digest probe is filed on the left, so it is not a target.** The flag is up for
the request the sub-run is serving, and the probe is that request's own digest input — so the
disclosing test holds at the carrier the entry would have been filed at, and the target test
denies exactly that. -/
theorem not_carrierRightKeep_digest (walk : Walk) (sk : SecretKey)
    (hpk : sk.publicKey = keyAt walk) (framed : Bytes) (answer : HashOutput)
    (mid : HandlerCarrier.State) (hframing : mid.framing = some framed)
    (entry : Bytes × HashOutput)
    (hdigest : entry.1 = Hashing.messageInput (Hashing.truncate answer) sk.publicKey framed) :
    ¬ carrierRightKeep walk entry.1 (servingNotice (keyAt walk) mid entry.1) := by
  rintro ⟨-, hnotFiled⟩
  refine hnotFiled ⟨framed, ?_, Hashing.truncate answer, ?_⟩
  · rw [framing_servingNotice]
    exact hframing
  · rw [hdigest, hpk]

end SlhDsaSecurity.CarrierRecord
