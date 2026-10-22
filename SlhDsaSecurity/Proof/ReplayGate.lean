import SlhDsaSecurity.Proof.RoutedSplit
import SlhDsaSecurity.Proof.CanonicalSignature
import SlhDsaSecurity.Proof.RandomizerGate

/-!
# The replay case is the signer's own signature, or a guess at `SK.prf`

`RoutedSplit.cases_of_win_three` leaves one branch standing: a forgery whose FORS part and
hypertree are the ones the signer writes for the digest it carries, whose fourteen positions are
all disclosed, and whose own message input is the only disclosure. This file turns that branch
into the one remaining charge.

The argument is short once the pieces are named. `Disclosed` supplies a cached input that
discloses the position `OnlySelfAt` fixes; `OnlySelfAt` identifies it as the forgery's own
message input; so that input is *signer-randomised*, which by
`CacheAvailability.randomizer_eq_of_signerRandomised` makes the forgery's randomiser the one the
signer derives for its message. A `Signature` has three fields, and the other two are canonical
by hypothesis, so the forgery is `Scheme.signInternal` on the nose, and its bytes are the bytes a
signing request would have returned.

What that leaves is a dichotomy about the log rather than about the signature. If the forgery's
message was signed, the log holds that pair and strong freshness fails — the forgery does not
win. If it was not, then the `PRF_msg` entry the signer would have made is nevertheless in the
cache, and nobody honest made it: key generation and the warm walk query structural inputs, and
the verifier never derives a randomiser. So the run queried `SK.prf ‖ PK.seed ‖ M` itself, with
the secret seed in the clear, and that is the guess `RandomizerGate` charges.

`RandomiserBad` is stated at the cache and the log, the two things the target's trace carries,
and not at the record: the record is where the charge is *paid*, and keeping the event off it
leaves the payment free to be read at whichever presentation of the run states the counting.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.ReplayGate

open Security CanonicalGraph CacheReplay Extraction VerifierProbes SplitCharged RoutedSplit

/-- The secret key the walk's three seeds generate, read from this run's own cache. -/
def secretKeyOf (x : Trace) : SecretKey :=
  ⟨x.1.1.1.1, x.1.1.1.2.1, keyOf x⟩

theorem secretKeyOf_publicKey (x : Trace) : (secretKeyOf x).publicKey = keyOf x := rfl

theorem keyOf_seed (x : Trace) : (keyOf x).seed = x.1.1.1.2.2 := rfl

/-! ## The forgery's own input is the signer's -/

/-- **A disclosing input is the forgery's own message input**, and so the forgery's message
input is signer-randomised. -/
theorem signerRandomised_of_replay {x : Trace} {message : Bytes} {parsed : Signature}
    (hdisclosed : Disclosed x message parsed) (honly : OnlySelfAt x message parsed) :
    CacheAvailability.SignerRandomised x.1.1.1.2.1 (keyOf x) x.2
      (Hashing.messageInput parsed.randomizer (keyOf x) message) := by
  obtain ⟨tree, honly⟩ := honly
  obtain ⟨input, answer, hsigner, hentry, hkey, other, hindex⟩ :=
    (CacheAvailability.mem_signedAt _ _ _ _ _).mp (hdisclosed tree)
  exact honly input answer hsigner hentry hkey ⟨other, hindex⟩ ▸ hsigner

/-- **The forgery's randomiser is the one the signer derives for its message.** -/
theorem randomizer_eq_of_replay {x : Trace} {message : Bytes} {parsed : Signature}
    (hdisclosed : Disclosed x message parsed) (honly : OnlySelfAt x message parsed) :
    parsed.randomizer =
      @Hashing.randomizer Id Id.instMonad (replayQuery x.2) x.1.1.1.2.1 (keyOf x).seed message :=
  CacheAvailability.randomizer_eq_of_signerRandomised _ _ _ _ _
    (signerRandomised_of_replay hdisclosed honly)

/-! ## So the forgery is the signature the signer writes -/

/-- **A replay forgery is `Scheme.signInternal` on its own message.** The randomiser comes from
the cache, the other two fields from `CanonicalAt`, and a `Signature` has no fourth field. -/
theorem eq_signInternal_of_replay {x : Trace} {message : Bytes} {parsed : Signature}
    (hcanonical : CanonicalAt x message parsed) (hdisclosed : Disclosed x message parsed)
    (honly : OnlySelfAt x message parsed) :
    parsed = @Scheme.signInternal Id Id.instMonad (replayQuery x.2) (secretKeyOf x) message := by
  refine @CanonicalSignature.eq_signInternal (replayQuery x.2) (secretKeyOf x) message parsed
    (randomizer_eq_of_replay hdisclosed honly) hcanonical.2.1 ?_
  rw [hcanonical.2.2, ← hcanonical.1]
  rfl

/-- **So its bytes are the bytes a signing request would have returned.** -/
theorem signature_eq_of_replay {x : Trace} {message : Bytes} {parsed : Signature}
    (hparsed : Signature.fromBytes? x.1.2.1.forgery.signature = some parsed)
    (hcanonical : CanonicalAt x message parsed) (hdisclosed : Disclosed x message parsed)
    (honly : OnlySelfAt x message parsed) :
    x.1.2.1.forgery.signature =
      (@Scheme.signInternal Id Id.instMonad (replayQuery x.2) (secretKeyOf x) message).toBytes :=
  @CanonicalSignature.signature_eq_toBytes (replayQuery x.2) (secretKeyOf x) message
    x.1.2.1.forgery.signature parsed hparsed
    (eq_signInternal_of_replay hcanonical hdisclosed honly)

/-! ## The dichotomy, and the event it leaves

What the log holds is the one thing the signature equation cannot supply, so it is named.
`LogFaithful` says each entry of the signing log carries the answer the signer computes for its
request, read at this run's own cache — which is the same answer it computed when the request
was made, because the cache only grows and a replayed query reads the entry that is there. -/

/-- Every logged request carries the signer's own answer. -/
def LogFaithful (x : Trace) : Prop :=
  ∀ entry ∈ x.1.2.1.signed, ∀ framed : Bytes, entry.1.frame = some framed →
    entry.2 = some
      (@Scheme.signInternal Id Id.instMonad (replayQuery x.2) (secretKeyOf x) framed).toBytes

/-- **The randomiser defect.** The cache holds the `PRF_msg` entry for a framing no signing
request produced — an entry whose input carries `SK.prf` in the clear, so the run that made it
guessed the secret seed. -/
def RandomiserBad (x : Trace) : Prop :=
  ∃ (message : Bytes) (answer : HashOutput),
    x.2 (Hashing.randomizerInput x.1.1.1.2.1 (keyOf x).seed message) = some answer ∧
      ¬ ∃ entry ∈ x.1.2.1.signed, entry.1.frame = some message

/-- **The replay case is the randomiser defect.** Either the forgery's message was signed, and
then the forgery is the pair the log returned, so it is not strongly fresh and does not win; or
it was not, and the `PRF_msg` entry its randomiser comes from is one no signing request made. -/
theorem randomiserBad_of_replay {x : Trace} (hfaithful : LogFaithful x)
    (hwin : Wins .strong x.1.2.1) (hreplay : ReplayForgery x) : RandomiserBad x := by
  classical
  obtain ⟨message, parsed, hframe, hparsed, hcanonical, hdisclosed, honly⟩ := hreplay
  obtain ⟨other, prfAnswer, hentry, hinput⟩ := signerRandomised_of_replay hdisclosed honly
  obtain ⟨-, -, hmessage⟩ := Hashing.messageInput_injective hinput
  subst hmessage
  by_cases hsigned : ∃ entry ∈ x.1.2.1.signed, entry.1.frame = some message
  · obtain ⟨entry, hmem, hentryFrame⟩ := hsigned
    exact absurd ⟨entry, hmem, Message.frame_injective hentryFrame hframe,
      by rw [hfaithful entry hmem message hentryFrame,
        signature_eq_of_replay hparsed hcanonical hdisclosed honly]⟩ hwin.2
  · exact ⟨message, prfAnswer, hentry, hsigned⟩

end SlhDsaSecurity.ReplayGate
