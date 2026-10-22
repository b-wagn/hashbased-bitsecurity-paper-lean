import SlhDsaSecurity.Proof.CarriedWitness
import SlhDsaSecurity.Proof.RandomizerGate

/-!
# The modified game's carrier, as a view rather than as a new handler

The hop compares the real carrier handler against one in which the signer's randomisers are
unreachable by the adversary's queries. The obvious way to build the second is to write a new
handler; the cheap way is to notice that the recorder reads its cache through
`RecorderView.CacheView` and nothing else.

**So the modification is a `CacheView` instance, and the whole stack above it is reused
verbatim** — `recorderOf`, `noticingRecorderOf`, `CountedHandler.withCount`, and every lemma
proved about them. The state is the real carrier beside a second table; `cacheOf` reads the
table for a `PRF_msg` input at the real seed **while a request is in flight**, and the carrier's
own cache otherwise; `update` writes to whichever of the two was read.

**Why the framing is in the condition.** The two games have to differ exactly when the adversary
asks at such an input and not when the signer does. The handler cannot tell who is asking from
the input alone — that is the whole difficulty of this hop — and the framing is the only thing in
the state that records it. `ServedAgreement.Files`' `stepFraming` and `runFraming` are what make
a request stay in flight for a whole sub-run, so "the signer's queries" is a well-defined set of
steps rather than a guess.

**The one law that has to be checked is `cache_update`**, and it holds because neither branch of
`update` touches the framing: the condition that decided where to write still decides where to
read. That is `cacheOf_splitUpdate` below, and it is the only place the construction could have
gone wrong silently — a `CacheView` whose two operations disagreed about the branch would still
typecheck.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.SplitSeedView

open Security RecorderView

/-- The modified game's carrier: the real one, beside a table for the signer's randomisers. -/
abbrev SplitCarrier : Type := HandlerCarrier.State × QueryCache HashSpec

/-- The queries the modified game answers from its table: `PRF_msg` inputs at the real seed,
asked while a request is in flight. -/
def FromTable (prfSeed : Digest) (state : SplitCarrier) (input : Bytes) : Prop :=
  state.1.framing ≠ none ∧ RandomizerGate.PrfClass prfSeed input

open scoped Classical in
/-- The cache the modified game answers from. -/
noncomputable def splitCacheOf (prfSeed : Digest) (state : SplitCarrier) :
    QueryCache HashSpec :=
  fun input => if FromTable prfSeed state input then state.2 input else state.1.cache input

open scoped Classical in
/-- And where it installs an answer: whichever of the two it would have read. -/
noncomputable def splitUpdate (prfSeed : Digest) (state : SplitCarrier) (input : Bytes)
    (answer : HashOutput) : SplitCarrier :=
  if FromTable prfSeed state input then (state.1, state.2.cacheQuery input answer)
  else (HandlerCarrier.cacheAnswer state.1 input answer, state.2)

/-- **Neither branch moves the framing**, so the condition that chose where to write still
chooses where to read. -/
theorem framing_splitUpdate (prfSeed : Digest) (state : SplitCarrier) (input : Bytes)
    (answer : HashOutput) : (splitUpdate prfSeed state input answer).1.framing =
      state.1.framing := by
  classical
  rw [splitUpdate]
  split
  · rfl
  · exact HandlerCarrier.framing_cacheAnswer state.1 input answer

/-- **So the table condition is unchanged by an update.** -/
theorem fromTable_splitUpdate (prfSeed : Digest) (state : SplitCarrier)
    (input probe : Bytes) (answer : HashOutput) :
    FromTable prfSeed (splitUpdate prfSeed state input answer) probe ↔
      FromTable prfSeed state probe := by
  rw [FromTable, FromTable, framing_splitUpdate]

open scoped Classical in
/-- **The view's one law.** Installing an answer caches it and says nothing else — the place
where a view whose two operations disagreed about the branch would have been caught. -/
theorem cacheOf_splitUpdate (prfSeed : Digest) (state : SplitCarrier) (input : Bytes)
    (answer : HashOutput) :
    splitCacheOf prfSeed (splitUpdate prfSeed state input answer) =
      (splitCacheOf prfSeed state).cacheQuery input answer := by
  classical
  funext probe
  by_cases hprobe : probe = input
  · subst hprobe
    rw [QueryCache.cacheQuery_self, splitCacheOf,
      if_congr (fromTable_splitUpdate prfSeed state probe probe answer) rfl rfl]
    by_cases htable : FromTable prfSeed state probe
    · rw [if_pos htable, splitUpdate, if_pos htable]
      show state.2.cacheQuery probe answer probe = some answer
      simp
    · rw [if_neg htable, splitUpdate, if_neg htable]
      show (HandlerCarrier.cacheAnswer state.1 probe answer).cache probe = some answer
      rw [HandlerCarrier.cache_cacheAnswer]
      simp
  · rw [QueryCache.cacheQuery_of_ne _ _ hprobe, splitCacheOf, splitCacheOf,
      if_congr (fromTable_splitUpdate prfSeed state input probe answer) rfl rfl]
    by_cases htable : FromTable prfSeed state probe
    · rw [if_pos htable, if_pos htable, splitUpdate]
      split
      · exact QueryCache.cacheQuery_of_ne _ _ hprobe
      · rfl
    · rw [if_neg htable, if_neg htable, splitUpdate]
      split
      · rfl
      · exact QueryCache.cacheQuery_of_ne _ _ hprobe

open scoped Classical in
/-- **The modified game's view.** Everything above it — `recorderOf`, `noticingRecorderOf`, the
counter — is the real game's, unchanged. -/
@[reducible] noncomputable def splitView (pk : PublicKey) (prfSeed : Digest) :
    CacheView SplitCarrier where
  cacheOf := splitCacheOf prfSeed
  update := splitUpdate prfSeed
  onQuery := fun state input => (CarriedWitness.servingNotice pk state.1 input, state.2)
  cache_update := cacheOf_splitUpdate prfSeed
  cache_onQuery := by
    intro state input
    funext probe
    rw [splitCacheOf, splitCacheOf, FromTable, FromTable,
      CarriedWitness.framing_servingNotice pk state.1 input]
    split
    · rfl
    · exact congrFun (CarriedWitness.cacheOf_servingNotice pk state.1 input) probe

end SlhDsaSecurity.SplitSeedView
