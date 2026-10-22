import SlhDsaSecurity.Proof.RecorderView
import SlhDsaSecurity.Proof.CoverageRouted
import SlhDsaSecurity.Proof.RandomizerGate

/-!
# The coverage event, read off the two recordings

The coverage charge is stated on a tape whose first block discloses and whose rest is targets,
and the game supplies the event at the final cache. This file is the join: it sends the
forgery's own digest to the *right* recording and each of its covering witnesses to the *left*
one, which is what makes the event a statement about coordinates of the two blocks.

**The join is stated over what discloses, not over one choice of it.** `Served` below takes the
disclosing test as a parameter, along with the class the target recording keeps, and asks of
them only what the join uses: the test grows with the cache, a disclosing input is of the
charged class, and a cached input of the charged class is in the narrowed one. The signer
instantiation — the test that reads `SK.prf`'s own `PRF_msg` entry out of the cache — follows
below, and the carrier's served set will be another application of the same lemmas rather than
a rewrite of them.

**The two sides are not symmetric, and the asymmetry is the whole content.**

*The target* is sent to the right recording by monotonicity. The disclosing test only becomes
truer as the cache grows, so an input that is not disclosing by the end was not disclosing when
it was queried either, and the left test cannot have fired on it. The event says exactly that
of the forgery's own digest, which is why it was put there.

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

/-! ## The join over an abstract disclosing test

Everything the join does is here. `served` is the left test, read at the state in force when a
query is answered; `narrow` is the class the right recording keeps, which is the charged class
less whatever the instantiation cannot file.

The state is a parameter, at `RecorderView.CacheView`. The reason is the disclosing test itself:
read at the cache, "the signer served this" is a question an adversary holding `SK.prf` can make
true with no request behind it, so `served` has to be allowed to read a state the signing oracle
alone writes. Nothing in this section cares which; it asks of the state only what the recorder
asks, which is how to see that a query is fresh and how to install an answer.

At `σ := QueryCache HashSpec` this is the join as it stood, because `RecorderView.recorderOf_cache`
says the recorder is the same one.

**`served` and `endKeep` are two predicates, and the reason is one sentence: a cache-readable
test is monotone because it is forgeable.** The filing test is read at the state a query is made
from, and the only kind an adversary cannot satisfy is one the signing oracle alone writes — a
flag it holds up while it serves. Such a flag is down again by the end of the run, so it cannot
also be what an entry satisfies at the end. The flag's non-monotonicity is not a defect to work
around; it is the same property that makes the false direction false. The two are joined by what
a step does rather than by being equal, and `mem_records_of_covered_of_mono` is the collapsed
case — one predicate in both roles — which is what a cache test allows and a flag does not. -/

namespace Served

open RecorderView

variable {σ : Type} [CacheView σ]

/-- The right test: an input of the narrowed class that is not disclosing. -/
def targetKeep (narrow : Bytes → Prop) (served : Bytes → σ → Prop) : Bytes → σ → Prop :=
  fun input view => narrow input ∧ ¬ served input view

/-- **The two tests cover the narrowed class**, so every fresh answer in it lands in exactly one
recording. -/
theorem cover (narrow : Bytes → Prop) (served : Bytes → σ → Prop)
    (input : Bytes) (view : σ) (hnarrow : narrow input) :
    served input view ∨ targetKeep narrow served input view := by
  classical
  by_cases hserved : served input view
  · exact Or.inl hserved
  · exact Or.inr ⟨hnarrow, hserved⟩

/-- The right test keeps the narrowed class. -/
theorem targetKeep_narrow (narrow : Bytes → Prop) (served : Bytes → σ → Prop) (input : Bytes)
    (view : σ) (hkeep : targetKeep narrow served input view) :
    narrow input := hkeep.1

/-- **The ordering defect.** Some target-recorded input is disclosing at the end. Read at
`endKeep`, since "at the end" is exactly where the filing test need not still hold. -/
def Late {α : Type} (endKeep : Bytes → σ → Prop) (result : α × StateOf σ) : Prop :=
  ∃ entry ∈ result.2.2.2, endKeep entry.1 result.2.1

set_option maxHeartbeats 800000 in
/-- **Off the defect, every disclosing entry is in the disclosing recording.** This is the
hypothesis `mem_records_of_covered` carries. -/
theorem disclosedRecorded_of_not_late (pk : PublicKey)
    (served endKeep : Bytes → σ → Prop) (narrow : Bytes → Prop)
    (computation : OracleComp OracleWorld (Outcome × Nat)) (start : σ)
    (result : (Outcome × Nat) × StateOf σ)
    (hmem : result ∈ support ((simulateQ (recorderOf served (targetKeep narrow served))
      computation).run (start, [], [])))
    (hfresh : ∀ input : Bytes, CombinedCharge.IsMessageInput pk input →
      CacheView.cacheOf start input = none)
    (hdisclosedClass : ∀ (input : Bytes) (inner : σ),
      endKeep input inner → CombinedCharge.IsMessageInput pk input)
    (hnarrowCached : ∀ (input : Bytes) (answer : HashOutput),
      CacheView.cacheOf result.2.1 input = some answer →
        CombinedCharge.IsMessageInput pk input → narrow input)
    (hlate : ¬ Late endKeep result) :
    ∀ (input : Bytes) (answer : HashOutput),
      endKeep input result.2.1 → CacheView.cacheOf result.2.1 input = some answer →
        (input, answer) ∈ result.2.2.1 := by
  classical
  intro input answer hserved hentry
  have hclass : CombinedCharge.IsMessageInput pk input := hdisclosedClass input result.2.1 hserved
  rcases mem_recordOf_of_cache served (targetKeep narrow served) narrow
    (fun probe inner hinner => cover narrow served probe inner hinner)
    computation (start, [], []) result hmem input answer
    (hnarrowCached input answer hentry hclass) (hfresh input hclass) hentry with hleft | hright
  · exact hleft
  · exact absurd ⟨(input, answer), hright, hserved⟩ hlate

set_option maxHeartbeats 800000 in
/-- **The covered forgery, as coordinates of the two recordings.** Its own digest is an entry of
the target recording and each of its covering witnesses is an entry of the disclosing one. -/
theorem mem_records_of_covered (pk : PublicKey)
    (served endKeep : Bytes → σ → Prop) (narrow : Bytes → Prop)
    (computation : OracleComp OracleWorld (Outcome × Nat)) (start : σ)
    (result : (Outcome × Nat) × StateOf σ)
    (hmem : result ∈ support ((simulateQ (recorderOf served (targetKeep narrow served))
      computation).run (start, [], [])))
    (hfresh : ∀ input : Bytes, CombinedCharge.IsMessageInput pk input →
      CacheView.cacheOf start input = none)
    (hfile : ∀ (input : Bytes) (view : σ) (answer : HashOutput),
      CacheView.cacheOf view input = none → served input view →
        endKeep input (CacheView.update view input answer))
    (hkeeps : ∀ (input probe : Bytes) (view : σ) (answer : HashOutput),
      CacheView.cacheOf view probe = none → endKeep input view →
        endKeep input (CacheView.update view probe answer))
    (hnarrowCached : ∀ (input : Bytes) (answer : HashOutput),
      CacheView.cacheOf result.2.1 input = some answer →
        CombinedCharge.IsMessageInput pk input → narrow input)
    (hdisclosedRecorded : ∀ (input : Bytes) (answer : HashOutput),
      endKeep input result.2.1 → CacheView.cacheOf result.2.1 input = some answer →
        (input, answer) ∈ result.2.2.1)
    (hcovered : CoverageRouted.ForgeryCoveredBy (fun input => endKeep input result.2.1) pk
      (result.1, CacheView.cacheOf result.2.1)) :
    ∃ target : Bytes × HashOutput, target ∈ result.2.2.2 ∧
      ∀ tree : MessageDigest.ForsTree, ∃ witness : Bytes × HashOutput,
        witness ∈ result.2.2.1 ∧ witness.1 ≠ target.1 ∧
          (MessageDigest.parse witness.2).1 = (MessageDigest.parse target.2).1 ∧
            (MessageDigest.parse witness.2).2 tree = (MessageDigest.parse target.2).2 tree := by
  classical
  obtain ⟨message, parsed, answer, hframe, hparsed, hentry, hnotself, hcoveredAt⟩ := hcovered
  have hclass : CombinedCharge.IsMessageInput pk
      (Hashing.messageInput parsed.randomizer pk message) := ⟨parsed.randomizer, message, rfl⟩
  have hnarrow := hnarrowCached (Hashing.messageInput parsed.randomizer pk message) answer
    hentry hclass
  have hside := mem_recordOf_of_cache served (targetKeep narrow served) narrow
    (fun input inner hinner => cover narrow served input inner hinner)
    computation (start, [], []) result hmem
    (Hashing.messageInput parsed.randomizer pk message) answer hnarrow
    (hfresh _ hclass) hentry
  have htarget : (Hashing.messageInput parsed.randomizer pk message, answer) ∈ result.2.2.2 := by
    rcases hside with hleft | hright
    · exact absurd (left_recordOf_endKeep_final served (targetKeep narrow served) endKeep
        hfile hkeeps computation (start, [], []) result hmem
        (fun entry hentry => absurd hentry (by simp)) _ hleft) hnotself
    · exact hright
  refine ⟨(Hashing.messageInput parsed.randomizer pk message, answer), htarget, fun tree => ?_⟩
  obtain ⟨other, otherAnswer, hne, hserved, hother, hinstance, hleaf⟩ := hcoveredAt tree
  exact ⟨(other, otherAnswer), hdisclosedRecorded other otherAnswer hserved hother, hne,
    hinstance, hleaf⟩

set_option maxHeartbeats 800000 in
/-- **The join, with the ordering defect named.** Off `Late` the covered forgery's digest is an
entry of the target recording and its witnesses are entries of the disclosing one, with nothing
left to assume about which query came first. -/
theorem mem_records_of_covered_of_not_late (pk : PublicKey)
    (served endKeep : Bytes → σ → Prop) (narrow : Bytes → Prop)
    (computation : OracleComp OracleWorld (Outcome × Nat)) (start : σ)
    (result : (Outcome × Nat) × StateOf σ)
    (hmem : result ∈ support ((simulateQ (recorderOf served (targetKeep narrow served))
      computation).run (start, [], [])))
    (hfresh : ∀ input : Bytes, CombinedCharge.IsMessageInput pk input →
      CacheView.cacheOf start input = none)
    (hfile : ∀ (input : Bytes) (view : σ) (answer : HashOutput),
      CacheView.cacheOf view input = none → served input view →
        endKeep input (CacheView.update view input answer))
    (hkeeps : ∀ (input probe : Bytes) (view : σ) (answer : HashOutput),
      CacheView.cacheOf view probe = none → endKeep input view →
        endKeep input (CacheView.update view probe answer))
    (hdisclosedClass : ∀ (input : Bytes) (inner : σ),
      endKeep input inner → CombinedCharge.IsMessageInput pk input)
    (hnarrowCached : ∀ (input : Bytes) (answer : HashOutput),
      CacheView.cacheOf result.2.1 input = some answer →
        CombinedCharge.IsMessageInput pk input → narrow input)
    (hlate : ¬ Late endKeep result)
    (hcovered : CoverageRouted.ForgeryCoveredBy (fun input => endKeep input result.2.1) pk
      (result.1, CacheView.cacheOf result.2.1)) :
    ∃ target : Bytes × HashOutput, target ∈ result.2.2.2 ∧
      ∀ tree : MessageDigest.ForsTree, ∃ witness : Bytes × HashOutput,
        witness ∈ result.2.2.1 ∧ witness.1 ≠ target.1 ∧
          (MessageDigest.parse witness.2).1 = (MessageDigest.parse target.2).1 ∧
            (MessageDigest.parse witness.2).2 tree = (MessageDigest.parse target.2).2 tree :=
  mem_records_of_covered pk served endKeep narrow computation start result hmem hfresh hfile
    hkeeps hnarrowCached
    (disclosedRecorded_of_not_late pk served endKeep narrow computation start result hmem hfresh
      hdisclosedClass hnarrowCached hlate)
    hcovered

set_option maxHeartbeats 800000 in
/-- **The collapsed case: one predicate in both roles.** A disclosing test that is monotone in
the view's cache can be its own end predicate, and the two laws are read off that monotonicity.
This is what a cache-readable test allows and a flag does not; it is stated so that the
instantiations which still use it need say nothing new, and so that the price of the general
form is visible as the exact gap between this and `mem_records_of_covered`. -/
theorem mem_records_of_covered_of_mono (pk : PublicKey)
    (served : Bytes → σ → Prop) (narrow : Bytes → Prop)
    (computation : OracleComp OracleWorld (Outcome × Nat)) (start : σ)
    (result : (Outcome × Nat) × StateOf σ)
    (hmem : result ∈ support ((simulateQ (recorderOf served (targetKeep narrow served))
      computation).run (start, [], [])))
    (hfresh : ∀ input : Bytes, CombinedCharge.IsMessageInput pk input →
      CacheView.cacheOf start input = none)
    (hmono : ∀ (input : Bytes) (inner later : σ),
      (∀ (probe : Bytes) (value : HashOutput),
        CacheView.cacheOf inner probe = some value →
          CacheView.cacheOf later probe = some value) →
      served input inner → served input later)
    (hnarrowCached : ∀ (input : Bytes) (answer : HashOutput),
      CacheView.cacheOf result.2.1 input = some answer →
        CombinedCharge.IsMessageInput pk input → narrow input)
    (hdisclosedRecorded : ∀ (input : Bytes) (answer : HashOutput),
      served input result.2.1 → CacheView.cacheOf result.2.1 input = some answer →
        (input, answer) ∈ result.2.2.1)
    (hcovered : CoverageRouted.ForgeryCoveredBy (fun input => served input result.2.1) pk
      (result.1, CacheView.cacheOf result.2.1)) :
    ∃ target : Bytes × HashOutput, target ∈ result.2.2.2 ∧
      ∀ tree : MessageDigest.ForsTree, ∃ witness : Bytes × HashOutput,
        witness ∈ result.2.2.1 ∧ witness.1 ≠ target.1 ∧
          (MessageDigest.parse witness.2).1 = (MessageDigest.parse target.2).1 ∧
            (MessageDigest.parse witness.2).2 tree = (MessageDigest.parse target.2).2 tree :=
  mem_records_of_covered pk served served narrow computation start result hmem hfresh
    (fun input view answer hviewFresh hkeep =>
      hmono input view (CacheView.update view input answer)
        (persists_update view input answer hviewFresh) hkeep)
    (fun input probe view answer hviewFresh hkeep =>
      hmono input view (CacheView.update view probe answer)
        (persists_update view probe answer hviewFresh) hkeep)
    hnarrowCached hdisclosedRecorded hcovered


/-! ## The weakening, and where the narrowed class is really needed

`mem_records_of_covered` asks `hnarrowCached` of **every** cached message input. That is one
demand per query, and `ObligationShapes.cover_of_served_or_narrow` was meant to retire all but
one of them: an input the left test already keeps is filed for that reason, so the class is
needed only at the target.

**The retirement works, but not where the design note put it.** `cover` is read inside
`RecorderView.mem_recordOf_of_cache` at the view in force when the input was answered *fresh*,
and that is earlier than the end. A witness disclosing at the **end** need not have been
disclosing **then**, and if it was neither disclosing nor narrow when answered it was filed on
neither side — a case `¬ Late` does not exclude, because `Late` speaks only of what the *target*
recording holds.

So the witnesses' demand does not vanish; it becomes `WitnessCover` below, which asks that an
input disclosing at the end was already keeping at every view where it was still fresh — or else
narrow. That is false of a cache test, by the same adversary that breaks the disclosing cap, and
**true by construction of a serving flag**, which is set when the request's own query is answered
and never cleared. It is therefore the sharp statement of what the carrier buys, and the reason
the carrier is not optional.

What is left over after it is one demand at one input: `NarrowTarget`, the forgery's own digest.
`narrowTarget_of_narrowCached` and `witnessCover_of_narrowCached` prove both are cases of the old
hypothesis, so this is visibly a weakening and not a different claim. -/

open scoped Classical in
/-- `RecorderView.mem_recordOf_of_cache` with the cover read only where it is used — at a view
where the input is still fresh. The proof is that one, unchanged but for passing the freshness it
already had in scope; it is here rather than beside the original only because this is the file
that needs it. -/
theorem mem_recordOf_of_cache_fresh {α : Type} (leftKeep rightKeep : Bytes → σ → Prop)
    (inClass : Bytes → Prop)
    (hcover : ∀ (input : Bytes) (view : σ), inClass input ->
      CacheView.cacheOf view input = none → leftKeep input view ∨ rightKeep input view)
    (computation : OracleComp OracleWorld α) (state : StateOf σ)
    (result : α × StateOf σ)
    (hmem : result ∈ support ((simulateQ (recorderOf leftKeep rightKeep) computation).run state))
    (input : Bytes) (answer : HashOutput) (hclass : inClass input)
    (hfresh : CacheView.cacheOf state.1 input = none)
    (hfinal : CacheView.cacheOf result.2.1 input = some answer) :
    (input, answer) ∈ result.2.2.1 ∨ (input, answer) ∈ result.2.2.2 := by
  classical
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [hmem] at hfinal
    rw [hfresh] at hfinal
    simp at hfinal
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    rcases queried with coin | probe
    · refine ih step.1 step.2 result hrest ?_ hfinal
      rw [recorderOf_step_inl leftKeep rightKeep coin state step hstep]
      exact hfresh
    · by_cases hsame : input = probe
      · subst hsame
        have hpersist : CacheView.cacheOf result.2.1 input = some step.1 :=
          recorderOf_cache_value_persists leftKeep rightKeep (next step.1) step.2 result hrest
            input step.1 (recorderOf_step_cache_self leftKeep rightKeep input state step hstep)
        have hvalue : step.1 = answer := by
          rw [hpersist] at hfinal
          exact Option.some.inj hfinal
        obtain ⟨hgrowLeft, hgrowRight⟩ :=
          recordOf_prefix leftKeep rightKeep (next step.1) step.2 result hrest
        have hrecStep := recorderOf_step_record leftKeep rightKeep input state step hstep
        by_cases hleft : leftKeep input state.1
        · refine Or.inl (hgrowLeft.subset ?_)
          rw [hrecStep, appendedOf_of_left leftKeep rightKeep input state step.1 hfresh hleft,
            hvalue]
          simp
        · have hright : rightKeep input state.1 := by
            rcases hcover input state.1 hclass hfresh with hcase | hcase
            · exact absurd hcase hleft
            · exact hcase
          refine Or.inr (hgrowRight.subset ?_)
          rw [hrecStep,
            appendedOf_of_right leftKeep rightKeep input state step.1 hfresh hleft hright,
            hvalue]
          simp
      · refine ih step.1 step.2 result hrest ?_ hfinal
        rcases recorderOf_step leftKeep rightKeep probe state step hstep with
          ⟨-, hshape⟩ | ⟨-, hshape⟩
        · rw [show step.2.1 = state.1 from by rw [hshape]]
          exact hfresh
        · rw [show step.2.1 = CacheView.update state.1 probe step.1 from by rw [hshape],
            cacheOf_update_of_ne state.1 probe input step.1 hsame]
          exact hfresh

/-- **The witnesses' demand.** An input the run discloses at the end, and whose answer the final
view holds, was already keeping at every view where it was still fresh -- or else is narrow. A
serving flag satisfies the left disjunct outright; a cache test does not. -/
def WitnessCover {α : Type} (served endKeep : Bytes → σ → Prop) (narrow : Bytes → Prop)
    (result : α × StateOf σ) : Prop :=
  ∀ (input : Bytes) (answer : HashOutput) (view : σ),
    endKeep input result.2.1 → CacheView.cacheOf result.2.1 input = some answer ->
      CacheView.cacheOf view input = none → served input view ∨ narrow input

/-- **The target's demand**, and the whole of what is left over: the forgery's own digest input
is narrow. One input, named by a single published object. -/
def NarrowTarget (pk : PublicKey) (narrow : Bytes → Prop)
    (result : (Outcome × Nat) × StateOf σ) : Prop :=
  ∀ (message : Bytes) (parsed : Signature),
    result.1.1.forgery.message.frame = some message ->
      Signature.fromBytes? result.1.1.forgery.signature = some parsed ->
        narrow (Hashing.messageInput parsed.randomizer pk message)

/-- **Both new demands are cases of the old one**, first half: the target's. -/
theorem narrowTarget_of_narrowCached (pk : PublicKey) (narrow : Bytes → Prop)
    (result : (Outcome × Nat) × StateOf σ)
    (hnarrowCached : ∀ (input : Bytes) (answer : HashOutput),
      CacheView.cacheOf result.2.1 input = some answer ->
        CombinedCharge.IsMessageInput pk input → narrow input)
    (hcached : ∀ (message : Bytes) (parsed : Signature),
      result.1.1.forgery.message.frame = some message ->
        Signature.fromBytes? result.1.1.forgery.signature = some parsed ->
          ∃ answer : HashOutput, CacheView.cacheOf result.2.1
            (Hashing.messageInput parsed.randomizer pk message) = some answer) :
    NarrowTarget pk narrow result := by
  intro message parsed hframe hparsed
  obtain ⟨answer, hentry⟩ := hcached message parsed hframe hparsed
  exact hnarrowCached _ answer hentry ⟨parsed.randomizer, message, rfl⟩

/-- **Both new demands are cases of the old one**, second half: the witnesses'. The old
hypothesis gives the right disjunct at every input it applies to, so nothing about the left test
is used -- which is the sense in which `WitnessCover` is weaker rather than different. -/
theorem witnessCover_of_narrowCached {α : Type} (pk : PublicKey)
    (served endKeep : Bytes → σ → Prop) (narrow : Bytes → Prop)
    (result : α × StateOf σ)
    (hdisclosedClass : ∀ (input : Bytes) (inner : σ),
      endKeep input inner → CombinedCharge.IsMessageInput pk input)
    (hnarrowCached : ∀ (input : Bytes) (answer : HashOutput),
      CacheView.cacheOf result.2.1 input = some answer ->
        CombinedCharge.IsMessageInput pk input → narrow input) :
    WitnessCover served endKeep narrow result :=
  fun input answer _ hend hentry _ =>
    Or.inr (hnarrowCached input answer hentry (hdisclosedClass input result.2.1 hend))

set_option maxHeartbeats 800000 in
/-- **Off the defect, every disclosing entry is in the disclosing recording** -- asking the
narrowed class of no input at all, only `WitnessCover`. -/
theorem disclosedRecorded_of_not_late_narrow {α : Type}
    (served endKeep : Bytes → σ → Prop)
    (narrow : Bytes → Prop) (computation : OracleComp OracleWorld α) (start : StateOf σ)
    (result : α × StateOf σ)
    (hmem : result ∈ support ((simulateQ (recorderOf served (targetKeep narrow served))
      computation).run start))
    (hcover : WitnessCover served endKeep narrow result)
    (hlate : ¬ Late endKeep result)
    (input : Bytes) (answer : HashOutput) (hserved : endKeep input result.2.1)
    (hentry : CacheView.cacheOf result.2.1 input = some answer)
    (hfresh : CacheView.cacheOf start.1 input = none) :
    (input, answer) ∈ result.2.2.1 := by
  classical
  rcases mem_recordOf_of_cache_fresh served (targetKeep narrow served)
    (fun probe => probe = input)
    (fun probe view hprobe hviewFresh => by
      subst hprobe
      rcases hcover probe answer view hserved hentry hviewFresh with hleft | hnarrow
      · exact Or.inl hleft
      · by_cases hkeep : served probe view
        · exact Or.inl hkeep
        · exact Or.inr ⟨hnarrow, hkeep⟩)
    computation start result hmem input answer rfl hfresh hentry with hleft | hright
  · exact hleft
  · exact absurd ⟨(input, answer), hright, hserved⟩ hlate

set_option maxHeartbeats 800000 in
/-- **The covered forgery, as coordinates of the two recordings, with the narrowing at one
input.** The witnesses pass through `WitnessCover`; only the forgery's own digest is asked to be
narrow, and that is the whole of what the shared half has to charge. -/
theorem mem_records_of_covered_narrow (pk : PublicKey)
    (served endKeep : Bytes → σ → Prop) (narrow : Bytes → Prop)
    (computation : OracleComp OracleWorld (Outcome × Nat)) (start : σ)
    (result : (Outcome × Nat) × StateOf σ)
    (hmem : result ∈ support ((simulateQ (recorderOf served (targetKeep narrow served))
      computation).run (start, [], [])))
    (hfresh : ∀ input : Bytes, CombinedCharge.IsMessageInput pk input ->
      CacheView.cacheOf start input = none)
    (hfile : ∀ (input : Bytes) (view : σ) (answer : HashOutput),
      CacheView.cacheOf view input = none → served input view ->
        endKeep input (CacheView.update view input answer))
    (hkeeps : ∀ (input probe : Bytes) (view : σ) (answer : HashOutput),
      CacheView.cacheOf view probe = none → endKeep input view ->
        endKeep input (CacheView.update view probe answer))
    (hdisclosedClass : ∀ (input : Bytes) (inner : σ),
      endKeep input inner → CombinedCharge.IsMessageInput pk input)
    (hcover : WitnessCover served endKeep narrow result)
    (hnarrowTarget : NarrowTarget pk narrow result)
    (hlate : ¬ Late endKeep result)
    (hcovered : CoverageRouted.ForgeryCoveredBy (fun input => endKeep input result.2.1) pk
      (result.1, CacheView.cacheOf result.2.1)) :
    ∃ target : Bytes × HashOutput, target ∈ result.2.2.2 ∧
      ∀ tree : MessageDigest.ForsTree, ∃ witness : Bytes × HashOutput,
        witness ∈ result.2.2.1 ∧ witness.1 ≠ target.1 ∧
          (MessageDigest.parse witness.2).1 = (MessageDigest.parse target.2).1 ∧
            (MessageDigest.parse witness.2).2 tree = (MessageDigest.parse target.2).2 tree := by
  classical
  obtain ⟨message, parsed, answer, hframe, hparsed, hentry, hnotself, hcoveredAt⟩ := hcovered
  have hclass : CombinedCharge.IsMessageInput pk
      (Hashing.messageInput parsed.randomizer pk message) := ⟨parsed.randomizer, message, rfl⟩
  have hnarrow := hnarrowTarget message parsed hframe hparsed
  have hside := mem_recordOf_of_cache_fresh served (targetKeep narrow served) narrow
    (fun probe view hprobe hviewFresh => by
      by_cases hkeep : served probe view
      · exact Or.inl hkeep
      · exact Or.inr ⟨hprobe, hkeep⟩)
    computation (start, [], []) result hmem
    (Hashing.messageInput parsed.randomizer pk message) answer hnarrow
    (hfresh _ hclass) hentry
  have htarget : (Hashing.messageInput parsed.randomizer pk message, answer) ∈ result.2.2.2 := by
    rcases hside with hleft | hright
    · exact absurd (left_recordOf_endKeep_final served (targetKeep narrow served) endKeep
        hfile hkeeps computation (start, [], []) result hmem
        (fun entry hentry => absurd hentry (by simp)) _ hleft) hnotself
    · exact hright
  refine ⟨(Hashing.messageInput parsed.randomizer pk message, answer), htarget, fun tree => ?_⟩
  obtain ⟨other, otherAnswer, hne, hservedOther, hother, hinstance, hleaf⟩ := hcoveredAt tree
  exact ⟨(other, otherAnswer),
    disclosedRecorded_of_not_late_narrow served endKeep narrow computation (start, [], []) result
      hmem hcover hlate other otherAnswer hservedOther hother
      (hfresh other (hdisclosedClass other result.2.1 hservedOther)),
    hne, hinstance, hleaf⟩

/-! ## The shape to aim a carrier at

`WitnessCover` above is a correct weakening of `hnarrowCached` and it is **not** the shape a
serving flag discharges. `HandlerCarrier.FilesLeft` reads the framing *in flight*, so it is false
at every view outside the request's own signing step — including views where the witness is still
fresh. A flag gives "disclosing at the end implies **filed**", not "implies keeping at every
earlier fresh view", and those differ exactly where the quantifier is.

What a flag gives is `hdisclosedRecorded` outright, and `mem_records_of_covered` already takes
that as a parameter. So the clean weakening is this one: the original with `hnarrowCached` cut
down to `NarrowTarget` and nothing else touched. `WitnessCover` survives as one sufficient
condition for `hdisclosedRecorded` off the ordering defect, useful at a cache test and not the
route a carrier should take.

Stating both, with this note between them, is the point: a weakening aimed at the wrong
quantifier is a bridge that does not meet, and that is only visible from the side that has to
supply it. -/

set_option maxHeartbeats 800000 in
/-- **The covered forgery, with the narrowed class asked at the forgery's digest and nowhere
else.** Everything the witnesses need is `hdisclosedRecorded`, exactly as before. -/
theorem mem_records_of_covered_narrowTarget (pk : PublicKey)
    (served endKeep : Bytes → σ → Prop) (narrow : Bytes → Prop)
    (computation : OracleComp OracleWorld (Outcome × Nat)) (start : σ)
    (result : (Outcome × Nat) × StateOf σ)
    (hmem : result ∈ support ((simulateQ (recorderOf served (targetKeep narrow served))
      computation).run (start, [], [])))
    (hfresh : ∀ input : Bytes, CombinedCharge.IsMessageInput pk input ->
      CacheView.cacheOf start input = none)
    (hfile : ∀ (input : Bytes) (view : σ) (answer : HashOutput),
      CacheView.cacheOf view input = none → served input view ->
        endKeep input (CacheView.update view input answer))
    (hkeeps : ∀ (input probe : Bytes) (view : σ) (answer : HashOutput),
      CacheView.cacheOf view probe = none → endKeep input view ->
        endKeep input (CacheView.update view probe answer))
    (hnarrowTarget : NarrowTarget pk narrow result)
    (hdisclosedRecorded : ∀ (input : Bytes) (answer : HashOutput),
      endKeep input result.2.1 → CacheView.cacheOf result.2.1 input = some answer ->
        (input, answer) ∈ result.2.2.1)
    (hcovered : CoverageRouted.ForgeryCoveredBy (fun input => endKeep input result.2.1) pk
      (result.1, CacheView.cacheOf result.2.1)) :
    ∃ target : Bytes × HashOutput, target ∈ result.2.2.2 ∧
      ∀ tree : MessageDigest.ForsTree, ∃ witness : Bytes × HashOutput,
        witness ∈ result.2.2.1 ∧ witness.1 ≠ target.1 ∧
          (MessageDigest.parse witness.2).1 = (MessageDigest.parse target.2).1 ∧
            (MessageDigest.parse witness.2).2 tree = (MessageDigest.parse target.2).2 tree := by
  classical
  obtain ⟨message, parsed, answer, hframe, hparsed, hentry, hnotself, hcoveredAt⟩ := hcovered
  have hnarrow := hnarrowTarget message parsed hframe hparsed
  have hside := mem_recordOf_of_cache_fresh served (targetKeep narrow served) narrow
    (fun probe view hprobe hviewFresh => by
      by_cases hkeep : served probe view
      · exact Or.inl hkeep
      · exact Or.inr ⟨hprobe, hkeep⟩)
    computation (start, [], []) result hmem
    (Hashing.messageInput parsed.randomizer pk message) answer hnarrow
    (hfresh _ ⟨parsed.randomizer, message, rfl⟩) hentry
  have htarget : (Hashing.messageInput parsed.randomizer pk message, answer) ∈ result.2.2.2 := by
    rcases hside with hleft | hright
    · exact absurd (left_recordOf_endKeep_final served (targetKeep narrow served) endKeep
        hfile hkeeps computation (start, [], []) result hmem
        (fun entry hentry => absurd hentry (by simp)) _ hleft) hnotself
    · exact hright
  refine ⟨(Hashing.messageInput parsed.randomizer pk message, answer), htarget, fun tree => ?_⟩
  obtain ⟨other, otherAnswer, hne, hservedOther, hother, hinstance, hleaf⟩ := hcoveredAt tree
  exact ⟨(other, otherAnswer), hdisclosedRecorded other otherAnswer hservedOther hother,
    hne, hinstance, hleaf⟩

end Served

/-! ## The signer instantiation

The disclosing test the recorder can run today reads the cache alone: the signer randomised
this input, in the sense that the `PRF_msg` entry its randomiser truncates from is there. What
it cannot see is the log, so the narrowed class has to exclude the `PRF_msg` inputs themselves,
and what that excludes is handed to the shared half rather than lost. -/

/-- The left test: the signer randomised this input, as the cache in force says. -/
def disclosingKeep (prfSeed : Digest) (pk : PublicKey) :
    Bytes → QueryCache HashSpec → Prop :=
  fun input cache => SignerRandomised prfSeed pk cache input

/-- The class the target recording keeps: the message class, less the `PRF_msg` inputs at the
real seed.

The last clause is what keeps a served request out of the target recording. The signer's own
`PRF_msg` query on a request framed as `PK.root ‖ m` *is* a message input, by the FIPS 205
format identity `FramingLeak.randomizerInput_eq_messageInput`, and it is not signer-randomised
when it is made; without the clause the recorder would file it as a target and the target count
would carry one unit per served request, which the budget has no room for. -/
def narrowClass (prfSeed : Digest) (pk : PublicKey) : Bytes → Prop :=
  fun input => CombinedCharge.IsMessageInput pk input ∧ ¬ RandomizerGate.PrfClass prfSeed input

/-- The right test at the signer instantiation. -/
def targetKeep (prfSeed : Digest) (pk : PublicKey) : Bytes → QueryCache HashSpec → Prop :=
  Served.targetKeep (narrowClass prfSeed pk) (disclosingKeep prfSeed pk)

/-- **The coverage event at the recorder's own disclosing test.** The extraction states the
event at the served class; this join reads it at the test the recorder decided by, so that
sending the forgery's digest to one recording and its witnesses to the other is a statement
about the same predicate the two blocks were filed under. -/
def CoveredAtKeep (prfSeed : Digest) (pk : PublicKey)
    (result : (Outcome × Nat) × QueryCache HashSpec) : Prop :=
  CoverageRouted.ForgeryCoveredBy (fun input => disclosingKeep prfSeed pk input result.2) pk
    result

/-- **The two tests cover the message class, less its `PRF_msg` part.** What the narrowing
leaves out is handed on rather than lost: an input in both classes has `SK.prf` for its
randomiser, which is the shared half's business. -/
theorem cover_messageInput (prfSeed : Digest) (pk : PublicKey) (input : Bytes)
    (cache : QueryCache HashSpec)
    (hclass : CombinedCharge.IsMessageInput pk input ∧ ¬ RandomizerGate.PrfClass prfSeed input) :
    disclosingKeep prfSeed pk input cache ∨ targetKeep prfSeed pk input cache :=
  Served.cover (narrowClass prfSeed pk) (disclosingKeep prfSeed pk) input cache hclass

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
    CombinedCharge.IsMessageInput pk input := hkeep.1.1

/-- The left test keeps the message class too. -/
theorem disclosingKeep_class (prfSeed : Digest) (pk : PublicKey) (input : Bytes)
    (cache : QueryCache HashSpec) (hkeep : disclosingKeep prfSeed pk input cache) :
    CombinedCharge.IsMessageInput pk input :=
  isMessageInput_of_signerRandomised prfSeed pk cache input hkeep

/-- **The case the narrowing hands on.** The run's cache holds a message input whose randomiser
is the signer's own `PRF_msg` seed — equivalently, a `PRF_msg` input at the real seed, by
`Hashing.randomizerInput_injective` read the other way.

Such an input falls outside the target test by construction, so neither the target it might be
nor the witness it might be is recorded. It is not charged here and cannot be: the seed is the
walk's, and at a fixed walk an adversary may carry it as a constant. It belongs to the shared
half, where the record's `PRF_msg` part is charged with the seed drawn after the run. -/
def SeedRandomised (prfSeed : Digest) (pk : PublicKey) (cache : QueryCache HashSpec) : Prop :=
  ∃ input : Bytes, cache input ≠ none ∧ CombinedCharge.IsMessageInput pk input ∧
    RandomizerGate.PrfClass prfSeed input

/-- Off that case, a cached message input is outside the `PRF_msg` class. -/
theorem not_prfClass_of_not_seedRandomised (prfSeed : Digest) (pk : PublicKey)
    (cache : QueryCache HashSpec) (hseed : ¬ SeedRandomised prfSeed pk cache) (input : Bytes)
    (hpresent : cache input ≠ none) (hclass : CombinedCharge.IsMessageInput pk input) :
    CombinedCharge.IsMessageInput pk input ∧ ¬ RandomizerGate.PrfClass prfSeed input :=
  ⟨hclass, fun hprf => hseed ⟨input, hpresent, hclass, hprf⟩⟩

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
def LateDisclosure {α : Type} (prfSeed : Digest) (pk : PublicKey)
    (result : α × SplitState) : Prop :=
  Served.Late (disclosingKeep prfSeed pk) result

set_option maxHeartbeats 800000 in
/-- **Off the defect, every disclosing entry is in the disclosing recording.** -/
theorem disclosedRecorded_of_not_late (prfSeed : Digest) (pk : PublicKey)
    (computation : OracleComp OracleWorld (Outcome × Nat)) (cache : QueryCache HashSpec)
    (result : (Outcome × Nat) × SplitState)
    (hmem : result ∈ support ((simulateQ (recorder (disclosingKeep prfSeed pk)
      (targetKeep prfSeed pk)) computation).run (cache, [], [])))
    (hfresh : ∀ input : Bytes, CombinedCharge.IsMessageInput pk input → cache input = none)
    (hseed : ¬ SeedRandomised prfSeed pk result.2.1)
    (hlate : ¬ LateDisclosure prfSeed pk result) :
    ∀ (input : Bytes) (answer : HashOutput),
      SignerRandomised prfSeed pk result.2.1 input → result.2.1 input = some answer →
        (input, answer) ∈ result.2.2.1 :=
  Served.disclosedRecorded_of_not_late pk (disclosingKeep prfSeed pk) (disclosingKeep prfSeed pk)
    (narrowClass prfSeed pk)
    computation cache result (by rw [RecorderView.recorderOf_cache]; exact hmem) hfresh
    (fun input inner hkeep => disclosingKeep_class prfSeed pk input inner hkeep)
    (fun input answer hentry hclass =>
      not_prfClass_of_not_seedRandomised prfSeed pk result.2.1 hseed input
        (Option.ne_none_iff_exists'.mpr ⟨answer, hentry⟩) hclass)
    hlate

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
/-- **The covered forgery, as coordinates of the two recordings.** -/
theorem mem_records_of_covered (prfSeed : Digest) (pk : PublicKey)
    (computation : OracleComp OracleWorld (Outcome × Nat)) (cache : QueryCache HashSpec)
    (result : (Outcome × Nat) × SplitState)
    (hmem : result ∈ support ((simulateQ (recorder (disclosingKeep prfSeed pk)
      (targetKeep prfSeed pk)) computation).run (cache, [], [])))
    (hfresh : ∀ input : Bytes, CombinedCharge.IsMessageInput pk input → cache input = none)
    (hseed : ¬ SeedRandomised prfSeed pk result.2.1)
    (hdisclosedRecorded : ∀ (input : Bytes) (answer : HashOutput),
      SignerRandomised prfSeed pk result.2.1 input → result.2.1 input = some answer →
        (input, answer) ∈ result.2.2.1)
    (hcovered : CoveredAtKeep prfSeed pk (result.1, result.2.1)) :
    ∃ target : Bytes × HashOutput, target ∈ result.2.2.2 ∧
      ∀ tree : MessageDigest.ForsTree, ∃ witness : Bytes × HashOutput,
        witness ∈ result.2.2.1 ∧ witness.1 ≠ target.1 ∧
          (MessageDigest.parse witness.2).1 = (MessageDigest.parse target.2).1 ∧
            (MessageDigest.parse witness.2).2 tree = (MessageDigest.parse target.2).2 tree :=
  Served.mem_records_of_covered_of_mono pk (disclosingKeep prfSeed pk) (narrowClass prfSeed pk)
    computation cache result (by rw [RecorderView.recorderOf_cache]; exact hmem) hfresh
    (fun input inner later hpersist hkeep =>
      disclosingKeep_mono prfSeed pk input inner later hpersist hkeep)
    (fun input answer hentry hclass =>
      not_prfClass_of_not_seedRandomised prfSeed pk result.2.1 hseed input
        (Option.ne_none_iff_exists'.mpr ⟨answer, hentry⟩) hclass)
    hdisclosedRecorded hcovered

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
    (hseed : ¬ SeedRandomised prfSeed pk result.2.1)
    (hlate : ¬ LateDisclosure prfSeed pk result)
    (hcovered : CoveredAtKeep prfSeed pk (result.1, result.2.1)) :
    ∃ target : Bytes × HashOutput, target ∈ result.2.2.2 ∧
      ∀ tree : MessageDigest.ForsTree, ∃ witness : Bytes × HashOutput,
        witness ∈ result.2.2.1 ∧ witness.1 ≠ target.1 ∧
          (MessageDigest.parse witness.2).1 = (MessageDigest.parse target.2).1 ∧
            (MessageDigest.parse witness.2).2 tree = (MessageDigest.parse target.2).2 tree :=
  mem_records_of_covered prfSeed pk computation cache result hmem hfresh hseed
    (disclosedRecorded_of_not_late prfSeed pk computation cache result hmem hfresh hseed hlate)
    hcovered

set_option maxHeartbeats 800000 in
/-- **The join, with the narrowing's leftover named rather than charged.** Either the run's
cache holds a message input whose randomiser is the signer's `PRF_msg` seed — which is a
`PRF_msg` input at the real seed, and is the shared half's to charge, with the seed drawn after
the run — or the covered forgery's digest is an entry of the target recording and each of its
witnesses an entry of the disclosing one.

The first case cannot be charged here. The seed belongs to the walk, this statement is read at
a fixed walk, and an adversary may carry the seed as a constant; a `2 ^ -128` defect on this
side would be a false statement in a small place. -/
theorem mem_records_or_seedRandomised (prfSeed : Digest) (pk : PublicKey)
    (computation : OracleComp OracleWorld (Outcome × Nat)) (cache : QueryCache HashSpec)
    (result : (Outcome × Nat) × SplitState)
    (hmem : result ∈ support ((simulateQ (recorder (disclosingKeep prfSeed pk)
      (targetKeep prfSeed pk)) computation).run (cache, [], [])))
    (hfresh : ∀ input : Bytes, CombinedCharge.IsMessageInput pk input → cache input = none)
    (hlate : ¬ LateDisclosure prfSeed pk result)
    (hcovered : CoveredAtKeep prfSeed pk (result.1, result.2.1)) :
    SeedRandomised prfSeed pk result.2.1 ∨
      ∃ target : Bytes × HashOutput, target ∈ result.2.2.2 ∧
        ∀ tree : MessageDigest.ForsTree, ∃ witness : Bytes × HashOutput,
          witness ∈ result.2.2.1 ∧ witness.1 ≠ target.1 ∧
            (MessageDigest.parse witness.2).1 = (MessageDigest.parse target.2).1 ∧
              (MessageDigest.parse witness.2).2 tree = (MessageDigest.parse target.2).2 tree := by
  classical
  by_cases hseed : SeedRandomised prfSeed pk result.2.1
  · exact Or.inl hseed
  · exact Or.inr (mem_records_of_covered_of_not_late prfSeed pk computation cache result hmem
      hfresh hseed hlate hcovered)

/-! ## The weakened join at the signer instantiation

The witnesses' demand and the target's, at the tests the game actually runs. `WitnessCover` stays
a hypothesis because it is what the serving flag is for: at a cache test it is false, by the
adversary that queries `randomizerInput prfSeed pk.seed m` and then
`messageInput (truncate answer) pk m` — the second input is disclosing when it is answered only
if the first was already cached, which is the adversary's own doing and not the signer's. -/

set_option maxHeartbeats 800000 in
/-- **The join with the narrowing at the forgery alone.** -/
theorem mem_records_of_covered_of_not_late_narrow (prfSeed : Digest) (pk : PublicKey)
    (computation : OracleComp OracleWorld (Outcome × Nat)) (cache : QueryCache HashSpec)
    (result : (Outcome × Nat) × SplitState)
    (hmem : result ∈ support ((simulateQ (RecorderView.recorderOf (disclosingKeep prfSeed pk)
      (targetKeep prfSeed pk)) computation).run (cache, [], [])))
    (hfresh : ∀ input : Bytes, CombinedCharge.IsMessageInput pk input → cache input = none)
    (hcover : Served.WitnessCover (disclosingKeep prfSeed pk) (disclosingKeep prfSeed pk)
      (narrowClass prfSeed pk) result)
    (hnarrowTarget : Served.NarrowTarget pk (narrowClass prfSeed pk) result)
    (hlate : ¬ LateDisclosure prfSeed pk result)
    (hcovered : CoveredAtKeep prfSeed pk (result.1, result.2.1)) :
    ∃ target : Bytes × HashOutput, target ∈ result.2.2.2 ∧
      ∀ tree : MessageDigest.ForsTree, ∃ witness : Bytes × HashOutput,
        witness ∈ result.2.2.1 ∧ witness.1 ≠ target.1 ∧
          (MessageDigest.parse witness.2).1 = (MessageDigest.parse target.2).1 ∧
            (MessageDigest.parse witness.2).2 tree = (MessageDigest.parse target.2).2 tree :=
  Served.mem_records_of_covered_narrow pk (disclosingKeep prfSeed pk) (disclosingKeep prfSeed pk)
    (narrowClass prfSeed pk) computation cache result hmem hfresh
    (fun input view answer hviewFresh hkeep =>
      disclosingKeep_mono prfSeed pk input view (RecorderView.CacheView.update view input answer)
        (RecorderView.persists_update view input answer hviewFresh) hkeep)
    (fun input probe view answer hviewFresh hkeep =>
      disclosingKeep_mono prfSeed pk input view (RecorderView.CacheView.update view probe answer)
        (RecorderView.persists_update view probe answer hviewFresh) hkeep)
    (fun input inner hkeep => disclosingKeep_class prfSeed pk input inner hkeep)
    hcover hnarrowTarget hlate hcovered

set_option maxHeartbeats 800000 in
/-- **The join with the narrowing at the forgery alone, taking the witnesses' containment
directly.** This is the one a carrier discharges: `hdisclosedRecorded` is what a serving flag
gives, and `NarrowTarget` is the leftover the shared half charges. -/
theorem mem_records_of_covered_narrowTarget (prfSeed : Digest) (pk : PublicKey)
    (computation : OracleComp OracleWorld (Outcome × Nat)) (cache : QueryCache HashSpec)
    (result : (Outcome × Nat) × SplitState)
    (hmem : result ∈ support ((simulateQ (RecorderView.recorderOf (disclosingKeep prfSeed pk)
      (targetKeep prfSeed pk)) computation).run (cache, [], [])))
    (hfresh : ∀ input : Bytes, CombinedCharge.IsMessageInput pk input → cache input = none)
    (hnarrowTarget : Served.NarrowTarget pk (narrowClass prfSeed pk) result)
    (hdisclosedRecorded : ∀ (input : Bytes) (answer : HashOutput),
      SignerRandomised prfSeed pk result.2.1 input → result.2.1 input = some answer →
        (input, answer) ∈ result.2.2.1)
    (hcovered : CoveredAtKeep prfSeed pk (result.1, result.2.1)) :
    ∃ target : Bytes × HashOutput, target ∈ result.2.2.2 ∧
      ∀ tree : MessageDigest.ForsTree, ∃ witness : Bytes × HashOutput,
        witness ∈ result.2.2.1 ∧ witness.1 ≠ target.1 ∧
          (MessageDigest.parse witness.2).1 = (MessageDigest.parse target.2).1 ∧
            (MessageDigest.parse witness.2).2 tree = (MessageDigest.parse target.2).2 tree :=
  Served.mem_records_of_covered_narrowTarget pk (disclosingKeep prfSeed pk)
    (disclosingKeep prfSeed pk) (narrowClass prfSeed pk) computation cache result hmem hfresh
    (fun input view answer hviewFresh hkeep =>
      disclosingKeep_mono prfSeed pk input view (RecorderView.CacheView.update view input answer)
        (RecorderView.persists_update view input answer hviewFresh) hkeep)
    (fun input probe view answer hviewFresh hkeep =>
      disclosingKeep_mono prfSeed pk input view (RecorderView.CacheView.update view probe answer)
        (RecorderView.persists_update view probe answer hviewFresh) hkeep)
    hnarrowTarget hdisclosedRecorded hcovered

/-! ## The join with the narrowed class left as a parameter

`narrowClass`'s `PRF_msg` clause is the whole of the answer half's leftover, and its retirement
is commissioned. The chain below leaves the class a parameter so that the retirement arrives as
an instantiation: at `narrowClass` the demand is the leftover and has to be charged, at
`CombinedCharge.IsMessageInput` it is discharged by `AnswerCoverage.narrowTarget_messageClass`
and there is nothing to charge. Neither reading rewrites the other. -/

set_option maxHeartbeats 800000 in
/-- **The join at the signer's disclosing test, with the target class a parameter.** -/
theorem mem_records_of_covered_of_not_late_class (prfSeed : Digest) (pk : PublicKey)
    (narrow : Bytes → Prop)
    (computation : OracleComp OracleWorld (Outcome × Nat)) (cache : QueryCache HashSpec)
    (result : (Outcome × Nat) × SplitState)
    (hmem : result ∈ support ((simulateQ (RecorderView.recorderOf (disclosingKeep prfSeed pk)
      (Served.targetKeep narrow (disclosingKeep prfSeed pk))) computation).run (cache, [], [])))
    (hfresh : ∀ input : Bytes, CombinedCharge.IsMessageInput pk input → cache input = none)
    (hcover : Served.WitnessCover (disclosingKeep prfSeed pk) (disclosingKeep prfSeed pk)
      narrow result)
    (hnarrowTarget : Served.NarrowTarget pk narrow result)
    (hlate : ¬ LateDisclosure prfSeed pk result)
    (hcovered : CoveredAtKeep prfSeed pk (result.1, result.2.1)) :
    ∃ target : Bytes × HashOutput, target ∈ result.2.2.2 ∧
      ∀ tree : MessageDigest.ForsTree, ∃ witness : Bytes × HashOutput,
        witness ∈ result.2.2.1 ∧ witness.1 ≠ target.1 ∧
          (MessageDigest.parse witness.2).1 = (MessageDigest.parse target.2).1 ∧
            (MessageDigest.parse witness.2).2 tree = (MessageDigest.parse target.2).2 tree :=
  Served.mem_records_of_covered_narrow pk (disclosingKeep prfSeed pk) (disclosingKeep prfSeed pk)
    narrow computation cache result hmem hfresh
    (fun input view answer hviewFresh hkeep =>
      disclosingKeep_mono prfSeed pk input view (RecorderView.CacheView.update view input answer)
        (RecorderView.persists_update view input answer hviewFresh) hkeep)
    (fun input probe view answer hviewFresh hkeep =>
      disclosingKeep_mono prfSeed pk input view (RecorderView.CacheView.update view probe answer)
        (RecorderView.persists_update view probe answer hviewFresh) hkeep)
    (fun input inner hkeep => disclosingKeep_class prfSeed pk input inner hkeep)
    hcover hnarrowTarget hlate hcovered

/-- **The target test keeps the class it is built from**, whatever that class is. -/
theorem targetKeep_class_of (prfSeed : Digest) (pk : PublicKey) (narrow : Bytes → Prop)
    (input : Bytes) (cache : QueryCache HashSpec)
    (hkeep : Served.targetKeep narrow (disclosingKeep prfSeed pk) input cache) : narrow input :=
  hkeep.1

end SlhDsaSecurity.SplitWitness
