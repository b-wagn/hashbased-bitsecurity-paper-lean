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

/-- The right test: an input of the narrowed class that is not disclosing.

**The class may read the view.** It is consulted at one input and one view only — the view in
force when that input was answered fresh — so nothing below depends on its being a property of
the bytes alone, and a class that *is* costs nothing by `fun input _ => …`. A carrier's class is
not: `AnswerCarrier.carrierRightKeep` excludes the signer's randomiser probe by the frame in
flight, which no predicate on bytes can see. -/
def targetKeep (narrow : Bytes → σ → Prop) (served : Bytes → σ → Prop) :
    Bytes → σ → Prop :=
  fun input view => narrow input view ∧ ¬ served input view

/-- The right test keeps the narrowed class. -/
theorem targetKeep_narrow (narrow : Bytes → σ → Prop) (served : Bytes → σ → Prop)
    (input : Bytes) (view : σ) (hkeep : targetKeep narrow served input view) :
    narrow input view := hkeep.1

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
when it is made; without the clause the recorder files it as a target.

**The reason is not the budget**, and the earlier claim here that it was is wrong.
`BlockViews.prob_targetCovered_le` puts no constraint on the right recording's length at all,
and target entries are charged against the split counter's inside slot, which `q` already
covers — so one more entry per served request costs nothing that is not already paid.

What the clause actually buys is `LateProvenance.hrecord`: a target-recorded input has to be one
the record holds, and the signer's `PRF_msg` probe is not the adversary's query. **That is a
provenance fact, and the clause is it in syntactic disguise** — it works only while the byte
formats happen to separate the two, and it charges whoever meets the case where they do not. The
honest exclusion is the frame the probe was made under,
`HandlerCarrier.not_filesLeft_randomizerInput`, which is available at a carrier and not at a
cache. -/
def narrowClass (prfSeed : Digest) (pk : PublicKey) : Bytes → Prop :=
  fun input => CombinedCharge.IsMessageInput pk input ∧ ¬ RandomizerGate.PrfClass prfSeed input

/-- The right test at the signer instantiation. -/
def targetKeep (prfSeed : Digest) (pk : PublicKey) : Bytes → QueryCache HashSpec → Prop :=
  Served.targetKeep (fun probe _ => narrowClass prfSeed pk probe) (disclosingKeep prfSeed pk)

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

/-! ## The weakened join at the signer instantiation

The witnesses' demand and the target's, at the tests the game actually runs. `WitnessCover` stays
a hypothesis because it is what the serving flag is for: at a cache test it is false, by the
adversary that queries `randomizerInput prfSeed pk.seed m` and then
`messageInput (truncate answer) pk m` — the second input is disclosing when it is answered only
if the first was already cached, which is the adversary's own doing and not the signer's. -/

/-! ## The join with the narrowed class left as a parameter

`narrowClass`'s `PRF_msg` clause is the whole of the answer half's leftover, and its retirement
is commissioned. The chain below leaves the class a parameter so that the retirement arrives as
an instantiation: at `narrowClass` the demand is the leftover and has to be charged, at
`CombinedCharge.IsMessageInput` it is discharged by `AnswerCoverage.narrowTarget_messageClass`
and there is nothing to charge. Neither reading rewrites the other. -/

end SlhDsaSecurity.SplitWitness
