import SlhDsaSecurity.Proof.SplitPrefix
import SlhDsaSecurity.Proof.CoverageRouted

/-!
# The coverage event, read off the two recordings

The coverage charge is stated on a tape whose first block discloses and whose rest is targets,
and the game supplies the event at the final cache. This file is the join: it sends the
forgery's own digest to the *right* recording and each of its covering witnesses to the *left*
one, which is what makes the event a statement about coordinates of the two blocks.

The two tests are the message class split by whether the signer randomised the input, taken at
the cache in force when the query was answered. They cover the class between them, so every
fresh message-class answer lands in exactly one recording.

**The two sides are not symmetric, and the asymmetry is the whole content.**

*The target* is sent to the right recording by monotonicity. `SignerRandomised` only becomes
truer as the cache grows, so a digest the signer has not randomised by the end was not
randomised when it was queried either, and the left test cannot have fired on it. The event
says exactly that of the forgery's own digest, which is why it was put there.

*The witnesses* are not reached that way, and they cannot be: the event says they are
disclosing at the *final* cache, while the recorder had to decide when the query was answered.
The two agree unless the adversary queried `H_msg` under a randomiser that a later `PRF_msg`
answer turned out to truncate to — it would have had to guess an answer it had not seen. That
case is a defect to be charged, not a step to be proved, and it is carried here as the
hypothesis `hdisclosedRecorded` so that the join does not pretend otherwise.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.SplitWitness

open Security CacheAvailability SplitPrefix

/-- The left test: the signer randomised this input, as the cache in force says. -/
def disclosingKeep (prfSeed : Digest) (pk : PublicKey) :
    Bytes → QueryCache HashSpec → Prop :=
  fun input cache => SignerRandomised prfSeed pk cache input

/-- The right test: a message-class input the signer did not randomise. -/
def targetKeep (prfSeed : Digest) (pk : PublicKey) : Bytes → QueryCache HashSpec → Prop :=
  fun input cache =>
    CombinedCharge.IsMessageInput pk input ∧ ¬ SignerRandomised prfSeed pk cache input

/-- **The two tests cover the message class.** -/
theorem cover_messageInput (prfSeed : Digest) (pk : PublicKey) (input : Bytes)
    (cache : QueryCache HashSpec) (hclass : CombinedCharge.IsMessageInput pk input) :
    disclosingKeep prfSeed pk input cache ∨ targetKeep prfSeed pk input cache := by
  classical
  by_cases hsigner : SignerRandomised prfSeed pk cache input
  · exact Or.inl hsigner
  · exact Or.inr ⟨hclass, hsigner⟩

/-- **The left test only becomes truer**, which is what sends a target that is not disclosing
at the end to the right recording. -/
theorem disclosingKeep_mono (prfSeed : Digest) (pk : PublicKey) (input : Bytes)
    (cache later : QueryCache HashSpec)
    (hpersist : ∀ (probe : Bytes) (value : HashOutput),
      cache probe = some value → later probe = some value)
    (hkeep : disclosingKeep prfSeed pk input cache) :
    disclosingKeep prfSeed pk input later :=
  signerRandomised_mono prfSeed pk hpersist input hkeep

/-- The right test keeps the message class. -/
theorem targetKeep_class (prfSeed : Digest) (pk : PublicKey) (input : Bytes)
    (cache : QueryCache HashSpec) (hkeep : targetKeep prfSeed pk input cache) :
    CombinedCharge.IsMessageInput pk input := hkeep.1

/-- The left test keeps the message class too. -/
theorem disclosingKeep_class (prfSeed : Digest) (pk : PublicKey) (input : Bytes)
    (cache : QueryCache HashSpec) (hkeep : disclosingKeep prfSeed pk input cache) :
    CombinedCharge.IsMessageInput pk input :=
  isMessageInput_of_signerRandomised prfSeed pk cache input hkeep

/-! ## The ordering defect, and what it really says

`mem_records_of_covered` asks that every disclosing entry of the final cache be in the
disclosing recording. What can go wrong is one thing only: an entry the recorder filed as a
target, because it was not disclosing when it was queried, which the run later made disclosing.
That is `LateDisclosure`, and on its complement the hypothesis holds.

Its content is an ordering, and the ordering is read off the recorder rather than off the story
about who queries what. `right_record_witness` hands back the cache in force when the entry was
filed; at that cache the `PRF_msg` entry for the entry's own message cannot have been present,
since entries never change and the entry is disclosing at the end. So the digest query came
first and the `PRF_msg` answer that discloses it was drawn afterwards — the adversary named a
randomiser before the answer it truncates existed. -/

/-- **The ordering defect.** Some target-recorded digest is disclosing at the end. -/
def LateDisclosure (prfSeed : Digest) (pk : PublicKey)
    (result : (Outcome × Nat) × SplitState) : Prop :=
  ∃ entry ∈ result.2.2.2, SignerRandomised prfSeed pk result.2.1 entry.1

set_option maxHeartbeats 800000 in
/-- **Off the defect, every disclosing entry is in the disclosing recording.** This is the
hypothesis `mem_records_of_covered` carries. -/
theorem disclosedRecorded_of_not_late (prfSeed : Digest) (pk : PublicKey)
    (computation : OracleComp OracleWorld (Outcome × Nat)) (cache : QueryCache HashSpec)
    (result : (Outcome × Nat) × SplitState)
    (hmem : result ∈ support ((simulateQ (recorder (disclosingKeep prfSeed pk)
      (targetKeep prfSeed pk)) computation).run (cache, [], [])))
    (hfresh : ∀ input : Bytes, CombinedCharge.IsMessageInput pk input → cache input = none)
    (hlate : ¬ LateDisclosure prfSeed pk result) :
    ∀ (input : Bytes) (answer : HashOutput),
      SignerRandomised prfSeed pk result.2.1 input → result.2.1 input = some answer →
        (input, answer) ∈ result.2.2.1 := by
  classical
  intro input answer hsigner hentry
  have hclass : CombinedCharge.IsMessageInput pk input :=
    isMessageInput_of_signerRandomised prfSeed pk result.2.1 input hsigner
  rcases mem_record_of_cache (disclosingKeep prfSeed pk) (targetKeep prfSeed pk)
    (CombinedCharge.IsMessageInput pk)
    (fun probe inner hinner => cover_messageInput prfSeed pk probe inner hinner)
    computation (cache, [], []) result hmem input answer hclass (hfresh input hclass) hentry with
    hleft | hright
  · exact hleft
  · exact absurd ⟨(input, answer), hright, hsigner⟩ hlate

set_option maxHeartbeats 800000 in
/-- **What the defect says about the order.** The `PRF_msg` entry whose answer discloses the
digest was absent when the digest was queried, and present at the end: the randomiser the query
carried was named before the answer it truncates to was drawn. -/
theorem late_ordering (prfSeed : Digest) (pk : PublicKey)
    (computation : OracleComp OracleWorld (Outcome × Nat)) (cache : QueryCache HashSpec)
    (result : (Outcome × Nat) × SplitState)
    (hmem : result ∈ support ((simulateQ (recorder (disclosingKeep prfSeed pk)
      (targetKeep prfSeed pk)) computation).run (cache, [], [])))
    (hlate : LateDisclosure prfSeed pk result) :
    ∃ (message : Bytes) (prfAnswer : HashOutput) (mid : QueryCache HashSpec),
      (∀ (probe : Bytes) (value : HashOutput),
          mid probe = some value → result.2.1 probe = some value) ∧
        mid (Hashing.randomizerInput prfSeed pk.seed message) = none ∧
          result.2.1 (Hashing.randomizerInput prfSeed pk.seed message) = some prfAnswer ∧
            mid (Hashing.messageInput (Hashing.truncate prfAnswer) pk message) = none := by
  classical
  obtain ⟨entry, hentry, hsigner⟩ := hlate
  rcases right_record_witness (disclosingKeep prfSeed pk) (targetKeep prfSeed pk) computation
    (cache, [], []) result hmem entry hentry with hnil | ⟨mid, hpersist, habsent, hright⟩
  · exact absurd hnil (by simp)
  obtain ⟨message, prfAnswer, hprf, hinput⟩ := hsigner
  refine ⟨message, prfAnswer, mid, hpersist, ?_, hprf, ?_⟩
  · by_contra hpresent
    obtain ⟨earlier, hearlier⟩ := Option.ne_none_iff_exists'.mp hpresent
    have hsame : earlier = prfAnswer := by
      have := hpersist _ _ hearlier
      rw [this] at hprf
      exact Option.some.inj hprf
    exact hright.2 ⟨message, earlier, hearlier, by rw [hsame]; exact hinput⟩
  · rw [← hinput]
    exact habsent

set_option maxHeartbeats 800000 in
/-- **The covered forgery, as coordinates of the two recordings.** Its own digest is an entry of
the target recording and each of its covering witnesses is an entry of the disclosing one. -/
theorem mem_records_of_covered (prfSeed : Digest) (pk : PublicKey)
    (computation : OracleComp OracleWorld (Outcome × Nat)) (cache : QueryCache HashSpec)
    (result : (Outcome × Nat) × SplitState)
    (hmem : result ∈ support ((simulateQ (recorder (disclosingKeep prfSeed pk)
      (targetKeep prfSeed pk)) computation).run (cache, [], [])))
    (hfresh : ∀ input : Bytes, CombinedCharge.IsMessageInput pk input → cache input = none)
    (hdisclosedRecorded : ∀ (input : Bytes) (answer : HashOutput),
      SignerRandomised prfSeed pk result.2.1 input → result.2.1 input = some answer →
        (input, answer) ∈ result.2.2.1)
    (hcovered : CoverageRouted.ForgeryDisclosedCovered prfSeed pk (result.1, result.2.1)) :
    ∃ target : Bytes × HashOutput, target ∈ result.2.2.2 ∧
      ∀ tree : MessageDigest.ForsTree, ∃ witness : Bytes × HashOutput,
        witness ∈ result.2.2.1 ∧ witness.1 ≠ target.1 ∧
          (MessageDigest.parse witness.2).1 = (MessageDigest.parse target.2).1 ∧
            (MessageDigest.parse witness.2).2 tree = (MessageDigest.parse target.2).2 tree := by
  classical
  obtain ⟨message, parsed, answer, hframe, hparsed, hentry, hnotself, hcoveredAt⟩ := hcovered
  have hclass : CombinedCharge.IsMessageInput pk
      (Hashing.messageInput parsed.randomizer pk message) := ⟨parsed.randomizer, message, rfl⟩
  have hside := mem_record_of_cache (disclosingKeep prfSeed pk) (targetKeep prfSeed pk)
    (CombinedCharge.IsMessageInput pk) (fun input inner hinner => cover_messageInput prfSeed pk
      input inner hinner) computation (cache, [], []) result hmem
    (Hashing.messageInput parsed.randomizer pk message) answer hclass
    (hfresh _ hclass) hentry
  have htarget : (Hashing.messageInput parsed.randomizer pk message, answer) ∈ result.2.2.2 := by
    rcases hside with hleft | hright
    · exact absurd (left_record_keep_final (disclosingKeep prfSeed pk) (targetKeep prfSeed pk)
        (fun input inner later hpersist hkeep =>
          disclosingKeep_mono prfSeed pk input inner later hpersist hkeep)
        computation (cache, [], []) result hmem (fun entry hentry => absurd hentry (by simp))
        _ hleft) hnotself
    · exact hright
  refine ⟨(Hashing.messageInput parsed.randomizer pk message, answer), htarget, fun tree => ?_⟩
  obtain ⟨other, otherAnswer, hne, hsigner, hother, hinstance, hleaf⟩ := hcoveredAt tree
  exact ⟨(other, otherAnswer), hdisclosedRecorded other otherAnswer hsigner hother, hne,
    hinstance, hleaf⟩

set_option maxHeartbeats 800000 in
/-- **The join, with the ordering defect named.** Off `LateDisclosure` the covered forgery's
digest is an entry of the target recording and its witnesses are entries of the disclosing one,
with nothing left to assume about which query came first. -/
theorem mem_records_of_covered_of_not_late (prfSeed : Digest) (pk : PublicKey)
    (computation : OracleComp OracleWorld (Outcome × Nat)) (cache : QueryCache HashSpec)
    (result : (Outcome × Nat) × SplitState)
    (hmem : result ∈ support ((simulateQ (recorder (disclosingKeep prfSeed pk)
      (targetKeep prfSeed pk)) computation).run (cache, [], [])))
    (hfresh : ∀ input : Bytes, CombinedCharge.IsMessageInput pk input → cache input = none)
    (hlate : ¬ LateDisclosure prfSeed pk result)
    (hcovered : CoverageRouted.ForgeryDisclosedCovered prfSeed pk (result.1, result.2.1)) :
    ∃ target : Bytes × HashOutput, target ∈ result.2.2.2 ∧
      ∀ tree : MessageDigest.ForsTree, ∃ witness : Bytes × HashOutput,
        witness ∈ result.2.2.1 ∧ witness.1 ≠ target.1 ∧
          (MessageDigest.parse witness.2).1 = (MessageDigest.parse target.2).1 ∧
            (MessageDigest.parse witness.2).2 tree = (MessageDigest.parse target.2).2 tree :=
  mem_records_of_covered prfSeed pk computation cache result hmem hfresh
    (disclosedRecorded_of_not_late prfSeed pk computation cache result hmem hfresh hlate)
    hcovered

end SlhDsaSecurity.SplitWitness
