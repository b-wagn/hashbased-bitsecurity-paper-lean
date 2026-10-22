import SlhDsaSecurity.Proof.AnswerCarrier

/-!
# The cover at a view with a request in flight

`CarrierClearFraming.clear_stages` discharges the target's demand at views with the framing
clear, which is the three stage starts and every adversary step. It does **not** discharge it
inside a signing sub-run: `ServedAgreement.startServingOn` raises the framing on purpose, so no
invariant of the form "nothing in flight" survives a sub-run, and
`SplitWitness.Served.mem_recordOf_of_cache_reaches` threads its `reaches` through every step to
reach the view the forgery's digest input is answered at. That is this file's subject: what the
cover needs at the views `clear_stages` does not reach.

**Both branches, and only one of them costs anything.** A sub-run serving frame `f` holds the
framing at `some f` throughout, by `ServedAgreement.Files.runFraming`. So at such a view, for the
forgery's digest input `messageInput r pk message`:

* if `f = message`, the input is **left-kept** — `HandlerCarrier.FilesLeft` compares against the
  frame in flight and this is that frame's own digest shape — so the cover's left disjunct fires
  and the demand is never consulted;
* if `f ≠ message`, the carrier's class holds **unless** that input is `f`'s randomiser input.

**And the second branch is a narrowing, not the old leftover.** The cache route needed
`¬ RandomizerGate.PrfClass prfSeed input`, which quantifies over every seed and every frame.
What is needed here is the negation at **one** frame — the one in flight — and at the real public
seed. `AnswerCarrier.filesRandomiser_prfClass` says the second implies the first and not
conversely, so the residue is strictly smaller: a coincidence between the forgery's digest input
and the randomiser input of a frame the signer actually served.

**What this file does not do is make that residue zero.** It is the same kind of event as
`AnswerCoverage.ForgerySeedRandomised` and has to be charged or excluded; `seedUnits := 0` is not
available on this route. What the carrier buys is that the demand is free wherever the framing is
clear and discharged outright where the frame matches, leaving the charge to one named case.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.CarrierDemand

open Security AnswerCarrier

/-- **The cover at a view with a request in flight.** The forgery's digest input is left-kept at
the frame it names, and off that frame it fails the carrier's randomiser clause only by
coinciding with the in-flight frame's own randomiser input. -/
theorem filesLeft_or_not_filesRandomiser (prfSeed : Digest) (pk : PublicKey)
    (randomizer : Digest) (message framed : Bytes) (view : HandlerCarrier.State)
    (hframing : view.framing = some framed)
    (hnotSeed : Hashing.messageInput randomizer pk message ≠
      Hashing.randomizerInput prfSeed pk.seed framed) :
    HandlerCarrier.FilesLeft pk view (Hashing.messageInput randomizer pk message) ∨
      ¬ FilesRandomiser prfSeed pk view (Hashing.messageInput randomizer pk message) := by
  by_cases hsame : framed = message
  · refine Or.inl ⟨framed, hframing, randomizer, ?_⟩
    rw [hsame]
  · refine Or.inr ?_
    rintro ⟨other, hother, hinput⟩
    rw [hframing] at hother
    rw [Option.some.injEq] at hother
    rw [← hother] at hinput
    exact hnotSeed hinput

/-- **The same, as the cover the recorder's two tests have to satisfy.** With the class free for
a message input, this is `leftKeep ∨ narrow` at an in-flight view, which is what
`SplitWitness.Served.cover` turns into `leftKeep ∨ targetKeep`. -/
theorem cover_inFlight (prfSeed : Digest) (pk : PublicKey) (randomizer : Digest)
    (message framed : Bytes) (view : HandlerCarrier.State)
    (hframing : view.framing = some framed)
    (hnotSeed : Hashing.messageInput randomizer pk message ≠
      Hashing.randomizerInput prfSeed pk.seed framed) :
    HandlerCarrier.FilesLeft pk view (Hashing.messageInput randomizer pk message) ∨
      (CombinedCharge.IsMessageInput pk (Hashing.messageInput randomizer pk message) ∧
        ¬ FilesRandomiser prfSeed pk view (Hashing.messageInput randomizer pk message)) :=
  (filesLeft_or_not_filesRandomiser prfSeed pk randomizer message framed view hframing
    hnotSeed).imp id fun hnot => ⟨⟨randomizer, message, rfl⟩, hnot⟩

/-- **And the residue really is narrower than the cache route's.** What has to be excluded here
is one frame's coincidence; what the cache route excluded was the class over all of them. -/
theorem prfClass_of_inFlight_coincidence (prfSeed : Digest) (pk : PublicKey)
    (randomizer : Digest) (message framed : Bytes)
    (hcoincide : Hashing.messageInput randomizer pk message =
      Hashing.randomizerInput prfSeed pk.seed framed) :
    RandomizerGate.PrfClass prfSeed (Hashing.messageInput randomizer pk message) :=
  ⟨pk.seed, framed, hcoincide⟩

end SlhDsaSecurity.CarrierDemand
