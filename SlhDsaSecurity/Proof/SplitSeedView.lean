import SlhDsaSecurity.Proof.CarriedWitness
import SlhDsaSecurity.Proof.RandomizerGate
import SlhDsaSecurity.Proof.SeedFlag
import SlhDsaSecurity.Proof.BracketedRun

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

/-! ## The correspondence, as a function rather than a relation

`HandlerComparison.prob_bad_eq` takes a relation between the two states and a `transfer` that
carries a left step's outcome to the right one. Both are much easier to supply if the relation
is **functional** — if the modified state is a function of the real one — and it can be, because
the only thing the modified game holds that the real one does not is *where* an entry is kept.

`splitOf` is that function: the real carrier's cache is split in two, the `PRF_msg` entries at
the real seed going to the table and everything else staying in the carrier. Then `rel` is an
equation and `transfer` is `splitOf` of the real game's own next state.

**And the split is exactly where the two games differ.** Read at a view with a request in
flight, `splitOf` gives back the real cache on every input — `splitCacheOf_splitOf_of_framing`
below. Read with nothing in flight, it gives back the real cache off the class and `none` on it:
the signer's randomisers are invisible to the adversary, which is the whole content of the hop,
and `splitCacheOf_splitOf_of_clear` is that sentence as an equation.
-/

open scoped Classical in
/-- The modified carrier a real one corresponds to: the same state, with its `PRF_msg` entries
at the real seed moved into the table. -/
noncomputable def splitOf (prfSeed : Digest) (carrier : HandlerCarrier.State) : SplitCarrier :=
  ({ cache := fun input =>
        if RandomizerGate.PrfClass prfSeed input then none else carrier.cache input,
      served := carrier.served,
      framing := carrier.framing },
    fun input => if RandomizerGate.PrfClass prfSeed input then carrier.cache input else none)

@[simp] theorem framing_splitOf (prfSeed : Digest) (carrier : HandlerCarrier.State) :
    (splitOf prfSeed carrier).1.framing = carrier.framing := rfl

@[simp] theorem served_splitOf (prfSeed : Digest) (carrier : HandlerCarrier.State) :
    (splitOf prfSeed carrier).1.served = carrier.served := rfl

open scoped Classical in
/-- **With a request in flight the two games read the same cache.** The signer sees its own
randomisers, wherever they are kept. -/
theorem splitCacheOf_splitOf_of_framing (prfSeed : Digest) (carrier : HandlerCarrier.State)
    (framed : Bytes) (hframing : carrier.framing = some framed) :
    splitCacheOf prfSeed (splitOf prfSeed carrier) = carrier.cache := by
  classical
  funext input
  rw [splitCacheOf, FromTable, framing_splitOf, hframing]
  by_cases hclass : RandomizerGate.PrfClass prfSeed input
  · rw [if_pos ⟨by simp, hclass⟩]
    show (if RandomizerGate.PrfClass prfSeed input then carrier.cache input else none) = _
    rw [if_pos hclass]
  · rw [if_neg (fun hboth => hclass hboth.2)]
    show (if RandomizerGate.PrfClass prfSeed input then none else carrier.cache input) = _
    rw [if_neg hclass]

open scoped Classical in
/-- **And with nothing in flight the `PRF_msg` entries are gone.** This is the hop's content:
what the signer cached at the real seed is not there for the adversary to find. -/
theorem splitCacheOf_splitOf_of_clear (prfSeed : Digest) (carrier : HandlerCarrier.State)
    (hclear : carrier.framing = none) (input : Bytes) :
    splitCacheOf prfSeed (splitOf prfSeed carrier) input =
      if RandomizerGate.PrfClass prfSeed input then none else carrier.cache input := by
  classical
  rw [splitCacheOf, FromTable, framing_splitOf, hclear,
    if_neg (fun hboth => hboth.1 rfl)]
  rfl

/-! ## The counter, at this view's own tupling

**The one place the table's placement costs something, and it is a trade rather than a snag.**
The view needs the table to compute `cacheOf`, so the table lives inside the view's state; and
`RecorderView.StateOf` then puts the carrier *behind* it, so the state is
`(HandlerCarrier.State × QueryCache) × Record × Record`. `CountedHandler.withCount` hard-codes
the carrier **first**, so it cannot see past the pair and does not apply.

That is the price of the decision that made everything else cheap — the modification being a
view is why `recorderOf`, `noticingRecorderOf` and every lemma about them were reused verbatim.
Paying it here, at one definition, is cheaper than paying it at the recorder.

`CountedHandler.run_reencode` is the general tool for exactly this and stays the right answer
when someone needs the counted shape itself. What is wanted here is narrower: a counter for one
handler, at one tupling, outside any induction. So it is written out, eight lines, with its run
equation by `rfl` — a failure here is a type error rather than a silent disagreement, which is
the property the re-encoding route would have given up.
-/

/-- The modified game's disclosing test: the real one, read at the carrier inside. -/
def splitDisclosingKeep (pk : PublicKey) : Bytes → SplitCarrier → Prop :=
  fun input state => CarriedWitness.disclosingKeep pk input state.1

/-- And its target test, lifted the same way. -/
def splitRightKeep (rightKeep : Bytes → HandlerCarrier.State → Prop) :
    Bytes → SplitCarrier → Prop :=
  fun input state => rightKeep input state.1

open scoped Classical in
/-- **The modified game's counted recorder.** `CountedHandler.withCount` at this view's tupling,
written out because the wrapper's own type cannot express it. -/
noncomputable def countedSplitRecorder (pk : PublicKey) (prfSeed : Digest)
    (rightKeep : Bytes → HandlerCarrier.State → Prop) :
    QueryImpl OracleWorld
      (StateT (SplitCarrier × ((DigestTape.Record × DigestTape.Record) × Nat)) ProbComp) :=
  fun queried state => do
    let step ← ((@noticingRecorderOf SplitCarrier (splitView pk prfSeed)
      (splitDisclosingKeep pk) (splitRightKeep rightKeep)) queried).run (state.1, state.2.1)
    pure (step.1, (step.2.1, (step.2.2, state.2.2 + Security.hashCost queried)))

open scoped Classical in
/-- **Its run, as the comparison reads it.** By `rfl`, as `CountedHandler.withCount_run` is. -/
theorem countedSplitRecorder_run (pk : PublicKey) (prfSeed : Digest)
    (rightKeep : Bytes → HandlerCarrier.State → Prop) (queried : OracleWorld.Domain)
    (state : SplitCarrier × ((DigestTape.Record × DigestTape.Record) × Nat)) :
    ((countedSplitRecorder pk prfSeed rightKeep) queried).run state =
      ((@noticingRecorderOf SplitCarrier (splitView pk prfSeed)
          (splitDisclosingKeep pk) (splitRightKeep rightKeep)) queried).run
            (state.1, state.2.1) >>= fun step =>
        (pure (step.1, (step.2.1, (step.2.2, state.2.2 + Security.hashCost queried))) :
          ProbComp (OracleWorld.Range queried ×
            (SplitCarrier × ((DigestTape.Record × DigestTape.Record) × Nat)))) := rfl

/-! ## The correspondence at the fused state, and the flag across it

`rel` is an equation, so it is given by the map below and `hbadIff` is `Iff.rfl`: the flag reads
the fused writer's record, and the split touches the carrier only. That the two sides' flags
agree is therefore not a property of the construction but of where the flag lives — which is why
`SeedFlag.RecordFlag` was stated at the fused state and generically in the handler's own.
-/

/-- The modified counted state a real one corresponds to. -/
noncomputable def splitStateOf (prfSeed : Digest) (state : BracketedRun.CountedState) :
    SplitCarrier × ((DigestTape.Record × DigestTape.Record) × Nat) :=
  (splitOf prfSeed state.1, state.2)

/-- And the same at the fused state, where the writer and the log ride along untouched. -/
noncomputable def splitFusedOf (prfSeed : Digest)
    (state : Multiplicative RecordedQueries.Tally × Security.SigningLog × BracketedRun.CountedState) :
    Multiplicative RecordedQueries.Tally × Security.SigningLog ×
      (SplitCarrier × ((DigestTape.Record × DigestTape.Record) × Nat)) :=
  (state.1, state.2.1, splitStateOf prfSeed state.2.2)

/-- **The flag crosses the correspondence by `rfl`.** It reads the writer, and the split moves
nothing but the carrier's cache. -/
theorem recordFlag_splitFusedOf (prfSeed : Digest)
    (state : Multiplicative RecordedQueries.Tally × Security.SigningLog × BracketedRun.CountedState) :
    SeedFlag.RecordFlag prfSeed state ↔
      SeedFlag.RecordFlag prfSeed (splitFusedOf prfSeed state) := Iff.rfl

/-! ## Neither handler fails

Generic in the view, because nothing about failing depends on which cache an answer comes from:
a coin samples, a hit is a `pure`, a miss is a map of a uniform draw. -/

open scoped Classical in
/-- **A step of the recorder that notices never fails, at any view.** -/
theorem noticingRecorderOf_step_mass {σ : Type} [RecorderView.CacheView σ]
    (leftKeep rightKeep : Bytes → σ → Prop) (queried : OracleWorld.Domain)
    (state : RecorderView.StateOf σ) :
    Pr[⊥ | ((RecorderView.noticingRecorderOf leftKeep rightKeep) queried).run state] = 0 := by
  classical
  rcases queried with coin | input
  · rw [RecorderView.noticingRecorderOf_run_inl, RecorderView.recorderOf_run_inl]
    simp
  · cases hcache : RecorderView.CacheView.cacheOf state.1 input with
    | some answer =>
      rw [RecorderView.noticingRecorderOf_run_inr_some leftKeep rightKeep input state answer
        hcache]
      simp
    | none =>
      rw [RecorderView.noticingRecorderOf_run_inr_none leftKeep rightKeep input state hcache]
      simp

open scoped Classical in
/-- **And so does the modified counted recorder's.** -/
theorem countedSplitRecorder_mass (pk : PublicKey) (prfSeed : Digest)
    (rightKeep : Bytes → HandlerCarrier.State → Prop) (queried : OracleWorld.Domain)
    (state : SplitCarrier × ((DigestTape.Record × DigestTape.Record) × Nat)) :
    Pr[⊥ | ((countedSplitRecorder pk prfSeed rightKeep) queried).run state] = 0 := by
  rw [countedSplitRecorder_run]
  exact (probFailure_bind_eq_zero_iff _ _).mpr
    ⟨@noticingRecorderOf_step_mass SplitCarrier (splitView pk prfSeed) _ _ queried _,
      fun _ _ => by simp⟩

/-! ## The two commutations the signing branch needs

With a request in flight the two handlers agree at every query, and `splitCacheOf_splitOf_of_framing`
is the half of that about *reading*. These are the half about **writing**: the split commutes with
the notice unconditionally, and with the install exactly while the framing is up.

**The second is the hop in one line.** `splitUpdate` at a split state and `splitOf` of a real
install are the same state when a request is in flight, and are *not* when the framing is down
and the input is of the class — the real game keeps the entry where the adversary can read it and
the modified game does not. So the condition on this lemma is not bookkeeping: it is the exact
boundary the whole comparison is built around, and a version without it would be false.
-/

open scoped Classical in
/-- **The split commutes with the notice**, unconditionally: the notice reads the framing and the
input's shape, and moves only the served set. -/
theorem splitOf_servingNotice (pk : PublicKey) (prfSeed : Digest)
    (carrier : HandlerCarrier.State) (input : Bytes) :
    splitOf prfSeed (CarriedWitness.servingNotice pk carrier input) =
      (CarriedWitness.servingNotice pk (splitOf prfSeed carrier).1 input,
        (splitOf prfSeed carrier).2) := by
  classical
  have hfiles : HandlerCarrier.FilesLeft pk (splitOf prfSeed carrier).1 input ↔
      HandlerCarrier.FilesLeft pk carrier input := by
    constructor
    · rintro ⟨framed, hframing, randomizer, hinput⟩
      exact ⟨framed, hframing, randomizer, hinput⟩
    · rintro ⟨framed, hframing, randomizer, hinput⟩
      exact ⟨framed, hframing, randomizer, hinput⟩
  rw [CarriedWitness.servingNotice, CarriedWitness.servingNotice]
  by_cases hfile : HandlerCarrier.FilesLeft pk carrier input
  · rw [if_pos hfile, if_pos (hfiles.mpr hfile)]
    rfl
  · rw [if_neg hfile, if_neg (fun hbad => hfile (hfiles.mp hbad))]

open scoped Classical in
/-- **And with the install, exactly while a request is in flight.** Without the framing this is
false, and its failure is the hop: with nothing in flight the real game keeps a `PRF_msg` entry
where the adversary can read it and the modified game does not. -/
theorem splitUpdate_splitOf (pk : PublicKey) (prfSeed : Digest)
    (carrier : HandlerCarrier.State) (framed : Bytes) (hframing : carrier.framing = some framed)
    (input : Bytes) (answer : HashOutput) :
    splitUpdate prfSeed (splitOf prfSeed carrier) input answer =
      splitOf prfSeed (HandlerCarrier.cacheAnswer carrier input answer) := by
  classical
  rw [splitUpdate, FromTable, framing_splitOf, hframing]
  by_cases hclass : RandomizerGate.PrfClass prfSeed input
  · rw [if_pos ⟨by simp, hclass⟩]
    refine Prod.ext ?_ ?_
    · refine congrArg (fun table : QueryCache HashSpec =>
        ({ cache := table, served := carrier.served,
           framing := carrier.framing } : HandlerCarrier.State)) ?_
      funext probe
      show (if RandomizerGate.PrfClass prfSeed probe then none else carrier.cache probe) =
        if RandomizerGate.PrfClass prfSeed probe then none
          else (carrier.cache.cacheQuery input answer) probe
      by_cases hprobe : RandomizerGate.PrfClass prfSeed probe
      · rw [if_pos hprobe, if_pos hprobe]
      · rw [if_neg hprobe, if_neg hprobe]
        refine (QueryCache.cacheQuery_of_ne _ _ ?_).symm
        rintro rfl
        exact hprobe hclass
    · funext probe
      show QueryCache.cacheQuery
          (fun p => if RandomizerGate.PrfClass prfSeed p then carrier.cache p else none)
          input answer probe =
        if RandomizerGate.PrfClass prfSeed probe
          then (carrier.cache.cacheQuery input answer) probe else none
      by_cases hprobe : probe = input
      · subst hprobe
        rw [QueryCache.cacheQuery_self, if_pos hclass, QueryCache.cacheQuery_self]
      · rw [QueryCache.cacheQuery_of_ne _ _ hprobe]
        by_cases hpc : RandomizerGate.PrfClass prfSeed probe
        · rw [if_pos hpc, if_pos hpc, QueryCache.cacheQuery_of_ne _ _ hprobe]
        · rw [if_neg hpc, if_neg hpc]
  · rw [if_neg (fun hboth => hclass hboth.2)]
    refine Prod.ext ?_ ?_
    · refine congrArg (fun table : QueryCache HashSpec =>
        ({ cache := table, served := carrier.served,
           framing := carrier.framing } : HandlerCarrier.State)) ?_
      funext probe
      show QueryCache.cacheQuery
          (fun p => if RandomizerGate.PrfClass prfSeed p then none else carrier.cache p)
          input answer probe =
        if RandomizerGate.PrfClass prfSeed probe then none
          else (carrier.cache.cacheQuery input answer) probe
      by_cases hprobe : probe = input
      · subst hprobe
        rw [QueryCache.cacheQuery_self, if_neg hclass, QueryCache.cacheQuery_self]
      · rw [QueryCache.cacheQuery_of_ne _ _ hprobe]
        by_cases hpc : RandomizerGate.PrfClass prfSeed probe
        · rw [if_pos hpc, if_pos hpc]
        · rw [if_neg hpc, if_neg hpc, QueryCache.cacheQuery_of_ne _ _ hprobe]
    · funext probe
      show (if RandomizerGate.PrfClass prfSeed probe then carrier.cache probe else none) =
        if RandomizerGate.PrfClass prfSeed probe
          then (carrier.cache.cacheQuery input answer) probe else none
      by_cases hpc : RandomizerGate.PrfClass prfSeed probe
      · rw [if_pos hpc, if_pos hpc]
        refine (QueryCache.cacheQuery_of_ne _ _ ?_).symm
        rintro rfl
        exact hclass hpc
      · rw [if_neg hpc, if_neg hpc]

end SlhDsaSecurity.SplitSeedView
