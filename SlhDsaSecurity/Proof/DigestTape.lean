import SlhDsaSecurity.Proof.ClassCharge
import SlhDsaSecurity.Proof.ForsLeaveOneOut
import SlhDsaSecurity.Proof.FreshDigest

/-!
# The adaptively recorded digest tape

Every FORS coverage bound in this development is proved about an *independent tape* of
uniform digest views — `ForsLeaveOneOut.independent_tape_coverage_le` is the leave-one-out
form, where each coordinate is charged against the disclosures of all the others.
`FreshDigest.prob_tape_event_le` transports such a bound to the shared oracle, but only for a
finite set of inputs *pinned in advance*. In the experiment no such set exists: the signing
oracle's `H_msg` inputs depend on the messages the adversary chooses and on the randomizers
it never sees, so the coordinates of the tape are selected adaptively during the run.

This file supplies the adaptive transport. The run is instrumented so that it records, in
query order, the input and answer of every query that both misses the cache and whose input
passes a test `keep` — in the experiment, "the input is in `H_msg` format". The recorded
answers are the tape; the inputs ride along because the leave-one-out charge needs two
coordinates to be *distinct*, and distinct inputs are what a game supplies
(`recordCovered_of_witnesses`, `mem_record_of_cache`). The content of the file is that the
recorded answers are distributed as a uniform tape:

* `prob_prefix_le` is the lazy-sampling invariant — any *fixed* word of length `k` is a
  prefix of the recorded list with probability at most `|HashOutput| ^ (-k)`. It is the
  adaptive analogue of `GrowthCharge.prob_cache_values_le`, with the pinned coordinates
  replaced by positions in the recording order, which is what removes the need to name the
  inputs in advance.
* `prob_tape_event_le` sums that over a set of words and pushes it through
  `FreshDigest.viewAssignment_uniform`: any event about the recorded tape of parsed views is
  no more likely than under a genuinely uniform tape.
* `prob_recordCovered_le` composes with `ForsLeaveOneOut.independent_tape_coverage_le`. A run
  that records at most `trials` answers ends holding a recorded digest whose fourteen FORS
  leaves are all disclosed by the other recorded digests with probability at most
  `1 / 2 ^ 141 + trials / 2 ^ 128` — one unit of `2 ^ -128` per recorded answer.
* `prob_recordCovered_within_le` and `prob_romEvent_le` state that in the vocabulary the other
  charges use: the tape length is supplied by `ClassCharge.GrowthAtMostOn keep`, since
  `record_length_le_growth` shows each recorded answer consumes one unit of that class's
  growth. So the rate is one unit of `2 ^ -128` per `keep`-class query, not per query.

The recording is padded with independent uniform values up to the tape length, so a run that
records fewer than `trials` answers still presents a full tape; coverage is monotone in the
disclosures, so the padding can only enlarge the event being charged.

`recorder_eq_rom` says the instrumentation is invisible: the recorded run and the plain run of
`KeygenUniform.rom` agree on every event about the result and the final cache, so a bound
proved here is a bound on the experiment.

The transport is an inequality rather than a distributional identity, and deliberately so. The
identity — `OracleComp.DeferredSampling.Factorizes`, the run equal in law to a front-drawn tape
followed by a tape-consuming run — is true, but it is strictly more than the composition needs,
since `ForsLeaveOneOut.independent_tape_coverage_le` is itself an inequality about a uniform
tape. What the composition needs is the one-sided statement that no event is *more* likely on
the recording than on a uniform tape, and that is what the prefix invariant delivers directly,
by the same route `GrowthCharge.prob_cache_values_le` takes for a pinned set.
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.DigestTape

/-! ## The recording oracle -/

/-- A recording: the inputs queried and the answers they drew, in query order. The input is
carried because the leave-one-out charge needs two coordinates of the tape to be *distinct*,
and distinct inputs are what the game supplies. -/
abbrev Record := List (Bytes × HashOutput)

/-- The cache together with the recording so far. -/
abbrev RecordState := QueryCache HashSpec × Record

/-- The answers of a recording, forgetting the inputs. This is the tape. -/
def answers (record : Record) : List HashOutput := record.map Prod.snd

@[simp] theorem answers_nil : answers [] = [] := rfl

@[simp] theorem answers_append (left right : Record) :
    answers (left ++ right) = answers left ++ answers right := List.map_append

@[simp] theorem answers_length (record : Record) : (answers record).length = record.length :=
  List.length_map _

@[simp] theorem answers_singleton (entry : Bytes × HashOutput) :
    answers [entry] = [entry.2] := rfl

theorem answers_getElem (record : Record) (i : Nat) (hi : i < (answers record).length) :
    (answers record)[i] = (record[i]'(by simpa using hi)).2 := List.getElem_map _

/-- A prefix of a recording has a prefix of its answers. -/
theorem answers_prefix {left right : Record} (hprefix : left <+: right) :
    answers left <+: answers right := hprefix.map _

open scoped Classical in
/-- The shared random oracle, recording the answer of every *fresh* query whose input passes
`keep`. A cache hit records nothing: it draws no randomness, so it contributes no tape
coordinate. -/
noncomputable def recorder (keep : Bytes → Prop) :
    QueryImpl OracleWorld (StateT RecordState ProbComp) :=
  fun queried state =>
    match queried with
    | Sum.inl coin => do
        let value ← ($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _)
        pure (value, state)
    | Sum.inr input => do
        let step ← (randomOracle input).run state.1
        pure (step.1, (step.2,
          if keep input ∧ state.1 input = none then state.2 ++ [(input, step.1)]
          else state.2))

open scoped Classical in
/-- On a private uniform sample the recording oracle draws and leaves the state alone. -/
theorem recorder_run_inl (keep : Bytes → Prop) (coin : unifSpec.Domain) (state : RecordState) :
    ((recorder keep) (Sum.inl coin)).run state =
      ($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _) >>= fun value =>
        (pure (value, state) : ProbComp _) := rfl

open scoped Classical in
/-- On a hash query the recording oracle is the shared oracle followed by the append. -/
theorem recorder_run_inr (keep : Bytes → Prop) (input : Bytes) (state : RecordState) :
    ((recorder keep) (Sum.inr input)).run state =
      (randomOracle input).run state.1 >>= fun step =>
        (pure (step.1, (step.2,
          if keep input ∧ state.1 input = none then state.2 ++ [(input, step.1)]
          else state.2)) :
          ProbComp _) := rfl

/-- The shared oracle on a private uniform sample. -/
theorem rom_run_inl (coin : unifSpec.Domain) (cache : QueryCache HashSpec) :
    (KeygenUniform.rom (Sum.inl coin)).run cache =
      ($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _) >>= fun value =>
        (pure (value, cache) : ProbComp _) := rfl

/-- The shared oracle on a hash query is the lazily sampled cache. -/
theorem rom_run_inr (input : Bytes) (cache : QueryCache HashSpec) :
    (KeygenUniform.rom (Sum.inr input)).run cache = (randomOracle input).run cache := rfl

/-- A block of `trials` independent uniform answers, used to pad a short recording out to a
full tape. -/
noncomputable def padding : Nat → ProbComp (List HashOutput)
  | 0 => pure []
  | n + 1 => do
      let value ← ($ᵗ HashOutput : ProbComp HashOutput)
      let rest ← padding n
      pure (value :: rest)

/-- The instrumented run from a given state, together with its independent padding block. -/
noncomputable def paddedFrom {α : Type} (keep : Bytes → Prop)
    (computation : OracleComp OracleWorld α) (state : RecordState) (trials : Nat) :
    ProbComp ((α × RecordState) × List HashOutput) := do
  let result ← (simulateQ (recorder keep) computation).run state
  let pad ← padding trials
  pure (result, pad)

/-- The instrumented run of a computation started from `cache` with an empty recording. -/
noncomputable def recordedRun {α : Type} (keep : Bytes → Prop)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    ProbComp (α × RecordState) :=
  (simulateQ (recorder keep) computation).run (cache, [])

/-- The padded run of a bind splits at the first step. -/
theorem paddedFrom_bind {α β : Type} (keep : Bytes → Prop)
    (computation : OracleComp OracleWorld α) (next : α → OracleComp OracleWorld β)
    (state : RecordState) (trials : Nat) :
    paddedFrom keep (computation >>= next) state trials =
      (simulateQ (recorder keep) computation).run state >>= fun step =>
        paddedFrom keep (next step.1) step.2 trials := by
  simp only [paddedFrom, simulateQ_bind, StateT.run_bind, bind_assoc]

/-! ## The instrumentation is invisible

The recording is a write-only component of the state: it never influences an answer, so the
instrumented run and the plain run of the shared oracle agree on every event that does not
mention it. -/

/-- The recording oracle and `KeygenUniform.rom` agree on every event about the result and the
final cache. -/
theorem recorder_eq_rom {α : Type} (keep : Bytes → Prop)
    (computation : OracleComp OracleWorld α) (state : RecordState)
    (event : α × QueryCache HashSpec → Prop) :
    Pr[fun result : α × RecordState => event (result.1, result.2.1) |
      (simulateQ (recorder keep) computation).run state] =
      Pr[event | (simulateQ KeygenUniform.rom computation).run state.1] := by
  classical
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure]
    rw [probEvent_pure, probEvent_pure]
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases queried with coin | input
    · rw [recorder_run_inl, rom_run_inl, bind_assoc, bind_assoc]
      simp only [pure_bind]
      rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
      exact tsum_congr fun value => by rw [ih value (state.1, state.2)]
    · rw [recorder_run_inr, rom_run_inr, bind_assoc]
      simp only [pure_bind]
      rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
      exact tsum_congr fun step => by
        rw [ih step.1 (step.2, if keep input ∧ state.1 input = none
          then state.2 ++ [(input, step.1)] else state.2)]

/-- The same statement for the run started with an empty recording. -/
theorem probEvent_recordedRun {α : Type} (keep : Bytes → Prop)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec)
    (event : α × QueryCache HashSpec → Prop) :
    Pr[fun result : α × RecordState => event (result.1, result.2.1) |
      recordedRun keep computation cache] =
      Pr[event | (simulateQ KeygenUniform.rom computation).run cache] :=
  recorder_eq_rom keep computation (cache, []) event

/-! ## The recording only grows -/

/-- Every recorded run is a run: dropping the recording lands in the support of the plain run
of the shared oracle. This is the support-level companion of `recorder_eq_rom`, and it is what
lets a fact proved about the game — a budget, a cache shape — be used under the
instrumentation. -/
theorem mem_support_rom {α : Type} (keep : Bytes → Prop)
    (computation : OracleComp OracleWorld α) (state : RecordState) (result : α × RecordState)
    (hmem : result ∈ support ((simulateQ (recorder keep) computation).run state)) :
    (result.1, result.2.1) ∈ support ((simulateQ KeygenUniform.rom computation).run state.1) := by
  classical
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, hmem]
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
    refine ⟨(step.1, step.2.1), ?_, ih step.1 step.2 result hrest⟩
    rcases queried with coin | input
    · rw [recorder_run_inl, mem_support_bind_iff] at hstep
      obtain ⟨value, hvalue, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [rom_run_inl, mem_support_bind_iff]
      refine ⟨value, hvalue, ?_⟩
      rw [support_pure, Set.mem_singleton_iff, hpure]
    · rw [recorder_run_inr, mem_support_bind_iff] at hstep
      obtain ⟨inner, hinner, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [rom_run_inr]
      have hshape : (step.1, step.2.1) = inner := by
        rw [hpure]
        rfl
      rw [hshape]
      exact hinner


/-- Recorded answers are appended, never changed: the starting record is a prefix of the
final one. -/
theorem record_prefix {α : Type} (keep : Bytes → Prop)
    (computation : OracleComp OracleWorld α) (state : RecordState) (result : α × RecordState)
    (hmem : result ∈ support ((simulateQ (recorder keep) computation).run state)) :
    state.2 <+: result.2.2 := by
  classical
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [hmem]
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    refine List.IsPrefix.trans ?_ (ih step.1 step.2 result hrest)
    rcases queried with coin | input
    · have hsame : step.2 = state := by
        rw [recorder_run_inl, mem_support_bind_iff] at hstep
        obtain ⟨value, -, hpure⟩ := hstep
        rw [support_pure, Set.mem_singleton_iff] at hpure
        exact congrArg Prod.snd hpure
      rw [hsame]
    · rw [recorder_run_inr, mem_support_bind_iff] at hstep
      obtain ⟨inner, -, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [hpure]
      by_cases hkeep : keep input ∧ state.1 input = none
      · simp [hkeep]
      · simp [hkeep]

/-- The same for the padded run: the starting record is a prefix of the padded recording. -/
theorem record_prefix_padded {α : Type} (keep : Bytes → Prop)
    (computation : OracleComp OracleWorld α) (state : RecordState) (trials : Nat)
    (result : (α × RecordState) × List HashOutput)
    (hmem : result ∈ support (paddedFrom keep computation state trials)) :
    state.2 <+: result.1.2.2 := by
  rw [paddedFrom, mem_support_bind_iff] at hmem
  obtain ⟨inner, hinner, hrest⟩ := hmem
  rw [mem_support_bind_iff] at hrest
  obtain ⟨pad, -, hpure⟩ := hrest
  rw [support_pure, Set.mem_singleton_iff] at hpure
  rw [hpure]
  exact record_prefix keep computation state inner hinner

/-! ## The recording is paid for by cache growth

Each recorded answer is one cache miss at a `keep`-class input, so the recording is no longer
than the run's growth *in that class*. This is what identifies the tape length with a budget
the experiment already carries: `ClassCharge.GrowthAtMostOn` is the per-class observable the
class-split charges are stated against, so the coverage term is charged at one unit per
message-class query rather than per query. -/

/-- Cache entries are never removed along a recorded run.

Presence only. `recorder_cache_value_persists` below is the same fact with the **value** named,
and is the one to reach for wherever the answer has to be related to anything: a conclusion that
an entry is there leaves a consumer to recover the value through `CacheReplay.replay`, which
answers a miss with `default`. -/
theorem recorder_cache_mono {α : Type} (keep : Bytes → Prop)
    (computation : OracleComp OracleWorld α) (state : RecordState) (result : α × RecordState)
    (hmem : result ∈ support ((simulateQ (recorder keep) computation).run state))
    (input : Bytes) (hpresent : state.1 input ≠ none) : result.2.1 input ≠ none := by
  classical
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [hmem]
    exact hpresent
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    refine ih step.1 step.2 result hrest ?_
    rcases queried with coin | queried
    · rw [recorder_run_inl, mem_support_bind_iff] at hstep
      obtain ⟨value, -, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [hpure]
      exact hpresent
    · rw [recorder_run_inr, mem_support_bind_iff] at hstep
      obtain ⟨inner, hinner, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [hpure]
      cases hqueried : state.1 queried with
      | none =>
        rw [QueryImpl.withCaching_run_none _ hqueried, support_map] at hinner
        obtain ⟨sampled, -, hpair⟩ := hinner
        have hmid : inner.2 = state.1.cacheQuery queried sampled :=
          (Prod.ext_iff.mp hpair).2.symm
        show inner.2 input ≠ none
        rw [hmid]
        by_cases hsame : input = queried
        · subst hsame
          rw [QueryCache.cacheQuery_self]
          simp
        · rw [QueryCache.cacheQuery_of_ne state.1 sampled hsame]
          exact hpresent
      | some cached =>
        rw [QueryImpl.withCaching_run_some _ hqueried, support_pure,
          Set.mem_singleton_iff] at hinner
        show inner.2 input ≠ none
        rw [hinner]
        exact hpresent

set_option maxHeartbeats 800000 in
/-- **The recording is no longer than the class growth.** Every recorded answer was installed at
a `keep`-class input that was absent from the starting cache, so the recording consumes that
class's growth budget one entry at a time. -/
theorem record_length_le_growth {α : Type} (keep : Bytes → Prop)
    (computation : OracleComp OracleWorld α) (state : RecordState) (limit : Nat)
    (result : α × RecordState)
    (hmem : result ∈ support ((simulateQ (recorder keep) computation).run state))
    (hgrowth : ClassCharge.GrowthAtMostOn keep state.1 result.2.1 limit) :
    result.2.2.length ≤ state.2.length + limit := by
  classical
  induction computation using OracleComp.inductionOn generalizing state limit result with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [hmem]
    simp
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    rcases queried with coin | input
    · rw [recorder_run_inl, mem_support_bind_iff] at hstep
      obtain ⟨value, -, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      have hsame : step.2 = state := congrArg Prod.snd hpure
      rw [← hsame] at hgrowth ⊢
      exact ih step.1 step.2 limit result hrest hgrowth
    · rw [recorder_run_inr, mem_support_bind_iff] at hstep
      obtain ⟨inner, hinner, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      cases hcached : state.1 input with
      | some cached =>
        rw [QueryImpl.withCaching_run_some _ hcached, support_pure,
          Set.mem_singleton_iff] at hinner
        have hstate : step.2 = state := by
          rw [hpure, hinner]
          refine Prod.ext rfl ?_
          exact if_neg (by rw [hcached]; simp)
        rw [← hstate] at hgrowth ⊢
        exact ih step.1 step.2 limit result hrest hgrowth
      | none =>
        rw [QueryImpl.withCaching_run_none _ hcached, support_map] at hinner
        obtain ⟨answer, -, hpair⟩ := hinner
        have hinnerCache : inner.2 = state.1.cacheQuery input answer :=
          (Prod.ext_iff.mp hpair).2.symm
        have hinnerAnswer : inner.1 = answer := (Prod.ext_iff.mp hpair).1.symm
        have hcacheStep : step.2.1 = state.1.cacheQuery input answer := by
          rw [hpure, ← hinnerCache]
        have hrecStep : step.2.2 =
            if keep input then state.2 ++ [(input, answer)] else state.2 := by
          rw [hpure, ← hinnerAnswer]
          simp [hcached]
        by_cases hkeep : keep input
        · have hpresent : result.2.1 input ≠ none := by
            refine recorder_cache_mono keep (next step.1) step.2 result hrest input ?_
            rw [hcacheStep, QueryCache.cacheQuery_self]
            simp
          have hpos : 1 ≤ limit := hgrowth.pos hkeep hcached hpresent
          have hnext : ClassCharge.GrowthAtMostOn keep step.2.1 result.2.1 (limit - 1) := by
            rw [hcacheStep]
            exact hgrowth.cacheQuery hkeep hcached hpresent
          have hstep' := ih step.1 step.2 (limit - 1) result hrest hnext
          rw [hrecStep, if_pos hkeep] at hstep'
          simp only [List.length_append, List.length_cons, List.length_nil] at hstep'
          omega
        · have hnext : ClassCharge.GrowthAtMostOn keep step.2.1 result.2.1 limit := by
            rw [hcacheStep]
            exact hgrowth.cacheQuery_other hkeep
          have hstep' := ih step.1 step.2 limit result hrest hnext
          rw [hrecStep, if_neg hkeep] at hstep'
          exact hstep'

/-- An installed answer persists verbatim along a recorded run. -/
theorem recorder_cache_value_persists {α : Type} (keep : Bytes → Prop)
    (computation : OracleComp OracleWorld α) (state : RecordState) (result : α × RecordState)
    (hmem : result ∈ support ((simulateQ (recorder keep) computation).run state))
    (input : Bytes) (answer : HashOutput) (hentry : state.1 input = some answer) :
    result.2.1 input = some answer := by
  classical
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [hmem]
    exact hentry
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    refine ih step.1 step.2 result hrest ?_
    rcases queried with coin | queried
    · rw [recorder_run_inl, mem_support_bind_iff] at hstep
      obtain ⟨value, -, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [hpure]
      exact hentry
    · rw [recorder_run_inr, mem_support_bind_iff] at hstep
      obtain ⟨inner, hinner, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [hpure]
      cases hqueried : state.1 queried with
      | none =>
        rw [QueryImpl.withCaching_run_none _ hqueried, support_map] at hinner
        obtain ⟨sampled, -, hpair⟩ := hinner
        have hmid : inner.2 = state.1.cacheQuery queried sampled :=
          (Prod.ext_iff.mp hpair).2.symm
        show inner.2 input = some answer
        rw [hmid]
        have hne : input ≠ queried := by
          intro hsame
          rw [hsame, hqueried] at hentry
          simp at hentry
        rw [QueryCache.cacheQuery_of_ne state.1 sampled hne]
        exact hentry
      | some cached =>
        rw [QueryImpl.withCaching_run_some _ hqueried, support_pure,
          Set.mem_singleton_iff] at hinner
        show inner.2 input = some answer
        rw [hinner]
        exact hentry

/-- **Every class answer the run installed was recorded.** An input of the class that was
absent from the starting cache and is present at the end was answered by a fresh draw, and
that draw is in the recording with the very input that asked for it. -/
theorem mem_record_of_cache {α : Type} (keep : Bytes → Prop)
    (computation : OracleComp OracleWorld α) (state : RecordState) (result : α × RecordState)
    (hmem : result ∈ support ((simulateQ (recorder keep) computation).run state))
    (input : Bytes) (answer : HashOutput) (hkeep : keep input)
    (hfresh : state.1 input = none) (hfinal : result.2.1 input = some answer) :
    (input, answer) ∈ result.2.2 := by
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
    rcases queried with coin | queried
    · rw [recorder_run_inl, mem_support_bind_iff] at hstep
      obtain ⟨value, -, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      have hsame : step.2 = state := congrArg Prod.snd hpure
      refine ih step.1 step.2 result hrest ?_ hfinal
      rw [hsame]
      exact hfresh
    · rw [recorder_run_inr, mem_support_bind_iff] at hstep
      obtain ⟨inner, hinner, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      cases hqueried : state.1 queried with
      | some cached =>
        rw [QueryImpl.withCaching_run_some _ hqueried, support_pure,
          Set.mem_singleton_iff] at hinner
        have hstate : step.2 = state := by
          rw [hpure, hinner]
          refine Prod.ext rfl ?_
          exact if_neg (by rw [hqueried]; simp)
        refine ih step.1 step.2 result hrest ?_ hfinal
        rw [hstate]
        exact hfresh
      | none =>
        rw [QueryImpl.withCaching_run_none _ hqueried, support_map] at hinner
        obtain ⟨sampled, -, hpair⟩ := hinner
        have hinnerCache : inner.2 = state.1.cacheQuery queried sampled :=
          (Prod.ext_iff.mp hpair).2.symm
        have hinnerAnswer : inner.1 = sampled := (Prod.ext_iff.mp hpair).1.symm
        have hcacheStep : step.2.1 = state.1.cacheQuery queried sampled := by
          rw [hpure, ← hinnerCache]
        by_cases hsame : input = queried
        · subst hsame
          have hstepEntry : step.2.1 input = some sampled := by
            rw [hcacheStep, QueryCache.cacheQuery_self]
          have hpersist : result.2.1 input = some sampled :=
            recorder_cache_value_persists keep (next step.1) step.2 result hrest input sampled
              hstepEntry
          have hvalue : sampled = answer := by
            rw [hpersist] at hfinal
            exact Option.some.inj hfinal
          have hrecStep : step.2.2 = state.2 ++ [(input, sampled)] := by
            rw [hpure, ← hinnerAnswer]
            exact if_pos ⟨hkeep, hfresh⟩
          have hgrow : step.2.2 <+: result.2.2 :=
            record_prefix keep (next step.1) step.2 result hrest
          refine hgrow.subset ?_
          rw [hrecStep, hvalue]
          simp
        · refine ih step.1 step.2 result hrest ?_ hfinal
          rw [hcacheStep, QueryCache.cacheQuery_of_ne state.1 sampled hsame]
          exact hfresh

/-! ## The lazy-sampling invariant

Any word fixed in advance is a prefix of what the run records with probability at most
`|HashOutput| ^ (-length)`: each of its letters has to be matched by one fresh uniform
answer. Nothing is assumed about *which* inputs the run queries — the coordinates are
positions in the recording order, not inputs, which is what removes the need to pin a finite
set of inputs in advance. -/

/-- The padding block alone matches a fixed word with the uniform probability. -/
theorem prob_padding_prefix_le (trials : Nat) (target : List HashOutput) :
    Pr[fun pad => target <+: pad | padding trials] ≤
      (1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^ target.length := by
  classical
  induction trials generalizing target with
  | zero =>
    cases target with
    | nil => simp
    | cons head tail =>
      refine le_of_eq_of_le (b := 0) ?_ (by simp)
      refine probEvent_eq_zero fun pad hpad hprefix => ?_
      rw [padding, support_pure, Set.mem_singleton_iff] at hpad
      subst hpad
      simp at hprefix
  | succ remaining ih =>
    cases target with
    | nil => simp
    | cons head tail =>
      have hrun : padding (remaining + 1) =
          ($ᵗ HashOutput : ProbComp HashOutput) >>= fun value =>
            padding remaining >>= fun rest => (pure (value :: rest) : ProbComp _) := rfl
      rw [hrun, probEvent_bind_eq_tsum]
      have hinner : ∀ value : HashOutput,
          Pr[fun pad => head :: tail <+: pad |
              padding remaining >>= fun rest => (pure (value :: rest) : ProbComp _)] ≤
            (if value = head then
              (1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^ tail.length else 0) := by
        intro value
        by_cases hhead : value = head
        · subst hhead
          rw [if_pos rfl]
          refine le_trans (le_of_eq ?_) (ih tail)
          rw [bind_pure_comp, probEvent_map]
          refine probEvent_congr' (fun rest _ => ?_) rfl
          simp [List.cons_prefix_cons]
        · rw [if_neg hhead]
          refine le_of_eq (probEvent_eq_zero fun pad hpad hprefix => ?_)
          rw [mem_support_bind_iff] at hpad
          obtain ⟨rest, -, hpure⟩ := hpad
          rw [support_pure, Set.mem_singleton_iff] at hpure
          subst hpure
          exact hhead (List.cons_prefix_cons.mp hprefix).1.symm
      calc ∑' value : HashOutput, Pr[= value | ($ᵗ HashOutput : ProbComp HashOutput)] *
            Pr[fun pad => head :: tail <+: pad |
              padding remaining >>= fun rest => (pure (value :: rest) : ProbComp _)]
          ≤ ∑' value : HashOutput, Pr[= value | ($ᵗ HashOutput : ProbComp HashOutput)] *
              (if value = head then
                (1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^ tail.length else 0) :=
            ENNReal.tsum_le_tsum fun value => mul_le_mul' le_rfl (hinner value)
        _ = Pr[= head | ($ᵗ HashOutput : ProbComp HashOutput)] *
              (1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^ tail.length := by
            rw [tsum_eq_single head (fun value hvalue => by simp [hvalue])]
            simp
        _ = _ := by
            rw [probOutput_uniformSample, List.length_cons, pow_succ, one_div]
            ring

set_option maxHeartbeats 1000000 in
/-- **The lazy-sampling invariant.** A word fixed in advance extends the starting record of
the instrumented run with probability at most `|HashOutput| ^ (-length)`. -/
theorem prob_prefix_le {α : Type} (keep : Bytes → Prop)
    (computation : OracleComp OracleWorld α) (trials : Nat) (state : RecordState)
    (target : List HashOutput) :
    Pr[fun result : (α × RecordState) × List HashOutput =>
        answers state.2 ++ target <+: answers result.1.2.2 ++ result.2 |
      paddedFrom keep computation state trials] ≤
      (1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^ target.length := by
  classical
  induction computation using OracleComp.inductionOn generalizing state target with
  | pure value =>
    have hrun : paddedFrom keep (pure value) state trials =
        padding trials >>= fun pad => (pure ((value, state), pad) : ProbComp _) := by
      rw [paddedFrom, simulateQ_pure, StateT.run_pure, pure_bind]
    rw [hrun, bind_pure_comp, probEvent_map]
    refine le_trans (le_of_eq ?_) (prob_padding_prefix_le trials target)
    refine probEvent_congr' (fun pad _ => ?_) rfl
    exact List.prefix_append_right_inj (answers state.2)
  | query_bind queried next ih =>
    rw [paddedFrom_bind, simulateQ_spec_query]
    rcases queried with coin | input
    · rw [recorder_run_inl, bind_assoc]
      simp only [pure_bind]
      rw [probEvent_bind_eq_tsum]
      calc ∑' value : OracleWorld.Range (Sum.inl coin),
            Pr[= value | ($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _)] *
              Pr[fun result : (α × RecordState) × List HashOutput =>
                  answers state.2 ++ target <+: answers result.1.2.2 ++ result.2 |
                paddedFrom keep (next value) state trials]
          ≤ ∑' value : OracleWorld.Range (Sum.inl coin),
              Pr[= value | ($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _)] *
                ((1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^ target.length) :=
            ENNReal.tsum_le_tsum fun value =>
              mul_le_mul' le_rfl (ih value state target)
        _ = (∑' value : OracleWorld.Range (Sum.inl coin),
              Pr[= value | ($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _)]) *
                ((1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^ target.length) :=
            ENNReal.tsum_mul_right
        _ ≤ 1 * ((1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^ target.length) :=
            mul_le_mul' tsum_probOutput_le_one le_rfl
        _ = _ := one_mul _
    · rw [recorder_run_inr, bind_assoc]
      simp only [pure_bind]
      cases hcached : state.1 input with
      | some cached =>
        have hrom : (randomOracle input).run state.1 =
            (pure (cached, state.1) : ProbComp (HashOutput × QueryCache HashSpec)) := by
          rw [QueryImpl.withCaching_run_some _ hcached]
        rw [hrom, pure_bind]
        simp only [reduceCtorEq, and_false, if_false]
        exact ih cached state target
      | none =>
        have hrom : (randomOracle input).run state.1 =
            (fun answer => (answer, state.1.cacheQuery input answer)) <$>
              ($ᵗ HashOutput : ProbComp HashOutput) := by
          rw [QueryImpl.withCaching_run_none _ hcached]
          simp [uniformSampleImpl]
        rw [hrom, bind_map_left]
        simp only [and_true]
        by_cases hkeep : keep input
        · simp only [if_pos hkeep]
          cases target with
          | nil => simp
          | cons head tail =>
            rw [probEvent_bind_eq_tsum]
            have hinner : ∀ answer : HashOutput,
                Pr[fun result : (α × RecordState) × List HashOutput =>
                    answers state.2 ++ head :: tail <+: answers result.1.2.2 ++ result.2 |
                  paddedFrom keep (next answer)
                    (state.1.cacheQuery input answer, state.2 ++ [(input, answer)]) trials] ≤
                  (if answer = head then
                    (1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^ tail.length else 0) := by
              intro answer
              by_cases hhead : answer = head
              · subst hhead
                rw [if_pos rfl]
                refine le_of_le_of_eq
                  (le_of_eq_of_le ?_
                    (ih answer (state.1.cacheQuery input answer,
                      state.2 ++ [(input, answer)]) tail))
                  rfl
                refine probEvent_congr' (fun result _ => ?_) rfl
                rw [answers_append, answers_singleton, List.append_assoc]
                rfl
              · rw [if_neg hhead]
                refine le_of_eq (probEvent_eq_zero fun result hresult hprefix => ?_)
                have hgrown : state.2 ++ [(input, answer)] <+: result.1.2.2 :=
                  record_prefix_padded keep (next answer)
                    (state.1.cacheQuery input answer, state.2 ++ [(input, answer)]) trials
                    result hresult
                have hgrownAnswers : answers state.2 ++ [answer] <+: answers result.1.2.2 := by
                  simpa using answers_prefix hgrown
                have hboth :
                    answers state.2 ++ [answer] <+: answers state.2 ++ head :: tail := by
                  refine List.prefix_of_prefix_length_le
                    (hgrownAnswers.trans (List.prefix_append _ _)) hprefix ?_
                  simp
                exact hhead (by
                  have := (List.prefix_append_right_inj (answers state.2)).mp hboth
                  simpa using (List.cons_prefix_cons.mp this).1)
            calc ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                  Pr[fun result : (α × RecordState) × List HashOutput =>
                      answers state.2 ++ head :: tail <+: answers result.1.2.2 ++ result.2 |
                    paddedFrom keep (next answer)
                      (state.1.cacheQuery input answer, state.2 ++ [(input, answer)]) trials]
                ≤ ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                    (if answer = head then
                      (1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^ tail.length else 0) :=
                  ENNReal.tsum_le_tsum fun answer => mul_le_mul' le_rfl (hinner answer)
              _ = Pr[= head | ($ᵗ HashOutput : ProbComp HashOutput)] *
                    (1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^ tail.length := by
                  rw [tsum_eq_single head (fun answer hanswer => by simp [hanswer])]
                  simp
              _ = _ := by
                  rw [probOutput_uniformSample, List.length_cons, pow_succ, one_div]
                  ring
        · simp only [if_neg hkeep]
          rw [probEvent_bind_eq_tsum]
          calc ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                Pr[fun result : (α × RecordState) × List HashOutput =>
                    answers state.2 ++ target <+: answers result.1.2.2 ++ result.2 |
                  paddedFrom keep (next answer)
                    (state.1.cacheQuery input answer, state.2) trials]
              ≤ ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                  ((1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^ target.length) :=
                ENNReal.tsum_le_tsum fun answer =>
                  mul_le_mul' le_rfl
                    (ih answer (state.1.cacheQuery input answer, state.2) target)
            _ = (∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)]) *
                  ((1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^ target.length) :=
                ENNReal.tsum_mul_right
            _ ≤ 1 * ((1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^ target.length) :=
                mul_le_mul' tsum_probOutput_le_one le_rfl
            _ = _ := one_mul _

/-! ## The recorded tape is uniform

Summing the invariant over a set of words and pushing the result through the parser turns it
into the statement the FORS results are phrased against: an event about the recorded tape of
parsed views is no more likely than the same event under a genuinely uniform tape. -/

/-- The padding block has exactly the length it was asked for. -/
theorem padding_length (trials : Nat) (pad : List HashOutput)
    (hmem : pad ∈ support (padding trials)) : pad.length = trials := by
  induction trials generalizing pad with
  | zero =>
    rw [padding, support_pure, Set.mem_singleton_iff] at hmem
    rw [hmem]
    rfl
  | succ remaining ih =>
    rw [show padding (remaining + 1) =
      ($ᵗ HashOutput : ProbComp HashOutput) >>= fun value =>
        padding remaining >>= fun rest => (pure (value :: rest) : ProbComp _) from rfl,
      mem_support_bind_iff] at hmem
    obtain ⟨value, -, hrest⟩ := hmem
    rw [mem_support_bind_iff] at hrest
    obtain ⟨rest, hrestMem, hpure⟩ := hrest
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [hpure, List.length_cons, ih rest hrestMem]

/-- Padding never fails. -/
theorem padding_neverFails (trials : Nat) : Pr[⊥ | padding trials] = 0 := by
  induction trials with
  | zero => rw [padding]; simp
  | succ remaining ih =>
    rw [show padding (remaining + 1) =
      ($ᵗ HashOutput : ProbComp HashOutput) >>= fun value =>
        padding remaining >>= fun rest => (pure (value :: rest) : ProbComp _) from rfl]
    simp

/-- The padding block is invisible to events about the run itself. -/
theorem probEvent_paddedFrom {α : Type} (keep : Bytes → Prop)
    (computation : OracleComp OracleWorld α) (state : RecordState) (trials : Nat)
    (event : α × RecordState → Prop) :
    Pr[fun result : (α × RecordState) × List HashOutput => event result.1 |
      paddedFrom keep computation state trials] =
      Pr[event | (simulateQ (recorder keep) computation).run state] := by
  classical
  rw [paddedFrom, probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  refine tsum_congr fun result => ?_
  rw [bind_pure_comp, probEvent_map]
  simp only [Function.comp_def]
  rw [probEvent_const, padding_neverFails, tsub_zero]
  split <;> simp

/-- Coordinatewise, a uniform word of answers has a uniform tape of parsed views. This is
`FreshDigest.viewAssignment_uniform` at the tape's own `Fin` index. -/
theorem viewTape_uniform (trials : Nat) :
    𝒟[(fun word index => MessageDigest.parse (word index)) <$>
        ($ᵗ (Fin trials → HashOutput) : ProbComp (Fin trials → HashOutput))] =
      𝒟[($ᵗ (ForsDisclosureTape.Tape trials) :
        ProbComp (ForsDisclosureTape.Tape trials))] := by
  classical
  let coordinate : HashOutput ≃ MessageDigest.View × (BitVec 2 × BitVec 7) :=
    Equiv.ofBijective MessageDigest.split MessageDigest.split_bijective
  let regroup : (Fin trials → HashOutput) ≃
      ForsDisclosureTape.Tape trials × (Fin trials → BitVec 2 × BitVec 7) :=
    (Equiv.piCongrRight (fun _ => coordinate)).trans
      (Equiv.arrowProdEquivProdArrow (Fin trials) (fun _ => MessageDigest.View)
        (fun _ => BitVec 2 × BitVec 7))
  have hmap : (fun word : Fin trials → HashOutput =>
        fun index => MessageDigest.parse (word index)) <$>
        ($ᵗ (Fin trials → HashOutput) : ProbComp (Fin trials → HashOutput)) =
      Prod.fst <$> (regroup <$> ($ᵗ (Fin trials → HashOutput) :
        ProbComp (Fin trials → HashOutput))) := by
    rw [Functor.map_map]
    rfl
  have hinner : 𝒟[regroup <$> ($ᵗ (Fin trials → HashOutput) :
        ProbComp (Fin trials → HashOutput))] =
      𝒟[($ᵗ (ForsDisclosureTape.Tape trials × (Fin trials → BitVec 2 × BitVec 7)) :
        ProbComp (ForsDisclosureTape.Tape trials × (Fin trials → BitVec 2 × BitVec 7)))] :=
    evalDist_map_bijective_uniform_cross (α := (Fin trials → HashOutput))
      (β := ForsDisclosureTape.Tape trials × (Fin trials → BitVec 2 × BitVec 7))
      regroup regroup.bijective
  rw [hmap, evalDist_map, hinner, ← evalDist_map]
  exact evalDist_map_fst_uniformSample_prod

/-- **A fixed set of tapes.** The probability that the padded recording begins with one of a
finite set of words is at most the uniform probability of that set. -/
theorem prob_tape_mem_le {α : Type} (keep : Bytes → Prop)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (trials : Nat)
    (bad : Finset (Fin trials → HashOutput)) :
    Pr[fun result : (α × RecordState) × List HashOutput =>
        ∃ word ∈ bad, List.ofFn word <+: answers result.1.2.2 ++ result.2 |
      paddedFrom keep computation (cache, []) trials] ≤
      bad.card * (1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^ trials := by
  classical
  refine le_trans (probEvent_exists_finset_le_sum bad _ _) ?_
  calc ∑ word ∈ bad,
        Pr[fun result : (α × RecordState) × List HashOutput =>
            List.ofFn word <+: answers result.1.2.2 ++ result.2 |
          paddedFrom keep computation (cache, []) trials]
      ≤ ∑ _word ∈ bad, (1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^ trials := by
        refine Finset.sum_le_sum fun word _ => ?_
        have hlen : (List.ofFn word).length = trials := List.length_ofFn
        refine le_of_le_of_eq (le_of_eq_of_le ?_
          (prob_prefix_le keep computation trials (cache, []) (List.ofFn word))) ?_
        · exact probEvent_congr' (fun _ _ => by simp) rfl
        · rw [hlen]
    _ = bad.card * (1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^ trials := by
        rw [Finset.sum_const, nsmul_eq_mul]

open scoped Classical in
/-- **The recorded tape is uniform.** Any event about the parsed views of the recorded tape is
no more likely than under a genuinely uniform tape of the same length. This is the adaptive
counterpart of `FreshDigest.prob_tape_event_le`, with the inputs no longer pinned in
advance. -/
theorem prob_tape_event_le {α : Type} (keep : Bytes → Prop)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (trials : Nat)
    (tapeBad : ForsDisclosureTape.Tape trials → Prop) :
    Pr[fun result : (α × RecordState) × List HashOutput =>
        ∃ word : Fin trials → HashOutput,
          tapeBad (fun i => MessageDigest.parse (word i)) ∧
            List.ofFn word <+: answers result.1.2.2 ++ result.2 |
      paddedFrom keep computation (cache, []) trials] ≤
      Pr[tapeBad | ($ᵗ (ForsDisclosureTape.Tape trials) :
        ProbComp (ForsDisclosureTape.Tape trials))] := by
  classical
  set bad : Finset (Fin trials → HashOutput) :=
    Finset.univ.filter (fun word => tapeBad (fun i => MessageDigest.parse (word i))) with hbad
  have hevent : Pr[fun result : (α × RecordState) × List HashOutput =>
      ∃ word : Fin trials → HashOutput,
        tapeBad (fun i => MessageDigest.parse (word i)) ∧
          List.ofFn word <+: answers result.1.2.2 ++ result.2 |
    paddedFrom keep computation (cache, []) trials] ≤
      bad.card * (1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^ trials := by
    refine le_trans (probEvent_mono ?_) (prob_tape_mem_le keep computation cache trials bad)
    rintro result - ⟨word, hword, hprefix⟩
    exact ⟨word, by simp [hbad, hword], hprefix⟩
  refine hevent.trans ?_
  have hcardFun : Fintype.card (Fin trials → HashOutput) =
      (Fintype.card HashOutput) ^ trials := by
    rw [Fintype.card_fun, Fintype.card_fin]
  have hcount : (bad.card : ℝ≥0∞) *
      (1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^ trials =
      Pr[fun word : Fin trials → HashOutput =>
        tapeBad (fun i => MessageDigest.parse (word i)) |
          ($ᵗ (Fin trials → HashOutput) : ProbComp (Fin trials → HashOutput))] := by
    rw [probEvent_uniformSample, hcardFun]
    push_cast
    rw [one_div, ← ENNReal.inv_pow, mul_comm, ← ENNReal.div_eq_inv_mul]
  rw [hcount]
  rw [show (fun word : Fin trials → HashOutput =>
      tapeBad (fun i => MessageDigest.parse (word i))) =
    tapeBad ∘ (fun word index => MessageDigest.parse (word index)) from rfl, ← probEvent_map]
  exact le_of_eq (probEvent_congr' (fun _ _ => Iff.rfl) (viewTape_uniform trials))

/-! ## The leave-one-out coverage event

`ForsLeaveOneOut.independent_tape_coverage_le` charges, on a uniform tape, the event that some
coordinate selected by a causal policy has its fourteen FORS leaves all disclosed by the other
coordinates. Taking the constant policy — every coordinate selected — gives the event in its
plainest form, and its expected number of selections is the tape length, so the charge is one
unit of `2 ^ -128` per coordinate. -/

/-- Some coordinate of the tape has its fourteen FORS leaves all disclosed by the others. -/
def TapeCovered {trials : Nat} (tape : ForsDisclosureTape.Tape trials) : Prop :=
  ∃ j, ForsCoverage.Covered (ForsDisclosureTape.disclosuresExcept j tape) (tape j)

/-- No policy selects more coordinates than the tape has. -/
theorem expectedUses_le {trials : Nat} (policy : ForsAdaptiveTargets.Policy trials) :
    ForsAdaptiveTargets.expectedUses policy ≤ (trials : ℝ≥0∞) := by
  classical
  calc ForsAdaptiveTargets.expectedUses policy
      ≤ ∑ tape : ForsAdaptiveTargets.Tape trials,
          Pr[= tape | ($ᵗ (ForsAdaptiveTargets.Tape trials) :
            ProbComp (ForsAdaptiveTargets.Tape trials))] * (trials : ℝ≥0∞) := by
        refine Finset.sum_le_sum fun tape _ => mul_le_mul' le_rfl ?_
        have huses : ForsAdaptiveTargets.uses policy tape ≤ trials := by
          unfold ForsAdaptiveTargets.uses
          exact le_trans (Finset.card_filter_le _ _) (by simp)
        exact Nat.cast_le.mpr huses
    _ = (∑ tape : ForsAdaptiveTargets.Tape trials,
          Pr[= tape | ($ᵗ (ForsAdaptiveTargets.Tape trials) :
            ProbComp (ForsAdaptiveTargets.Tape trials))]) * (trials : ℝ≥0∞) :=
        (Finset.sum_mul _ _ _).symm
    _ ≤ 1 * (trials : ℝ≥0∞) :=
        mul_le_mul' (le_trans (ENNReal.sum_le_tsum _) tsum_probOutput_le_one) le_rfl
    _ = _ := one_mul _

/-- **The uniform tape is covered rarely.** On a uniform tape of `trials` views, the
probability that some coordinate is covered by the others is at most
`1 / 2 ^ 141 + trials / 2 ^ 128`. -/
theorem prob_tapeCovered_le (trials : Nat) (htrials : trials ≤ 5 * 2 ^ 62) :
    Pr[TapeCovered | ($ᵗ (ForsDisclosureTape.Tape trials) :
      ProbComp (ForsDisclosureTape.Tape trials))] ≤
      (1 : ℝ≥0∞) / 2 ^ 141 + (trials : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  have hmain := ForsLeaveOneOut.independent_tape_coverage_le trials htrials (fun _ _ => true)
  have hevent : Pr[TapeCovered | ($ᵗ (ForsDisclosureTape.Tape trials) :
      ProbComp (ForsDisclosureTape.Tape trials))] =
      Pr[fun tape => ∃ j, (fun _ _ => true) j (ForsAdaptiveTargets.history tape j) = true ∧
        ForsCoverage.Covered (ForsDisclosureTape.disclosuresExcept j tape) (tape j) |
        ($ᵗ (ForsAdaptiveTargets.Tape trials) :
          ProbComp (ForsAdaptiveTargets.Tape trials))] :=
    probEvent_congr' (fun tape _ => by simp [TapeCovered]) rfl
  rw [hevent]
  refine hmain.trans (add_le_add le_rfl ?_)
  exact ENNReal.div_le_div_right (expectedUses_le _) _

/-! ## From the recording to the tape

A recorded list is read as a tape of its own length. Because coverage is monotone in the
disclosures, a covered recording stays covered inside any longer word extending it, so the
record's coverage event is charged by the full tape's. -/

/-- The parsed FORS views of a recorded list, as a tape of its own length. -/
def recordTape (record : Record) : ForsDisclosureTape.Tape record.length :=
  fun i => MessageDigest.parse (record[i.val]).2

/-- Some recorded digest has its fourteen FORS leaves all disclosed by the other recorded
digests. -/
def RecordCovered (record : Record) : Prop := TapeCovered (recordTape record)

/-- **Coverage from witnesses.** A distinguished recorded entry whose fourteen FORS leaves are
each matched, at the same FORS instance, by a recorded entry queried at a *different* input is
covered by the rest of the recording. Distinct inputs are what the game supplies, and distinct
entries are what the leave-one-out charge needs; the two meet here because the recording
carries the input beside the answer. -/
theorem recordCovered_of_witnesses (record : Record) (target : Bytes) (answer : HashOutput)
    (htarget : (target, answer) ∈ record)
    (hothers : ∀ tree : MessageDigest.ForsTree, ∃ other : Bytes × HashOutput,
      other ∈ record ∧ other.1 ≠ target ∧
        (MessageDigest.parse other.2).1 = (MessageDigest.parse answer).1 ∧
        (MessageDigest.parse other.2).2 tree = (MessageDigest.parse answer).2 tree) :
    RecordCovered record := by
  classical
  obtain ⟨j, hj, hjvalue⟩ := List.getElem_of_mem htarget
  refine ⟨⟨j, hj⟩, fun tree => ?_⟩
  obtain ⟨other, hmem, hne, hinstance, hleaf⟩ := hothers tree
  obtain ⟨k, hk, hkvalue⟩ := List.getElem_of_mem hmem
  have htargetView : recordTape record ⟨j, hj⟩ = MessageDigest.parse answer := by
    show MessageDigest.parse (record[j]).2 = _
    rw [hjvalue]
  have hotherView : recordTape record ⟨k, hk⟩ = MessageDigest.parse other.2 := by
    show MessageDigest.parse (record[k]).2 = _
    rw [hkvalue]
  have hindex : (⟨k, hk⟩ : Fin record.length) ≠ ⟨j, hj⟩ := by
    intro hsame
    have hval : k = j := congrArg Fin.val hsame
    subst hval
    exact hne (congrArg Prod.fst (hkvalue.symm.trans hjvalue))
  simp only [ForsDisclosureTape.disclosuresExcept, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact ⟨⟨k, hk⟩, ⟨hindex, by rw [hotherView, htargetView]; exact hinstance⟩,
    by rw [hotherView, htargetView]; exact hleaf⟩

/-- Coverage within a recording persists in any word that extends it. -/
theorem tapeCovered_of_prefix {trials : Nat} (record : Record)
    (word : Fin trials → HashOutput) (hpre : answers record <+: List.ofFn word)
    (hcov : RecordCovered record) :
    TapeCovered (fun i => MessageDigest.parse (word i)) := by
  classical
  have hlen : record.length ≤ trials := by
    have hle := hpre.length_le
    rw [List.length_ofFn, answers_length] at hle
    exact hle
  have hget : ∀ i : Fin record.length,
      word ⟨i.val, lt_of_lt_of_le i.isLt hlen⟩ = (record[i.val]).2 := by
    intro i
    have hlt : i.val < (answers record).length := by simp [i.isLt]
    have hstep := hpre.getElem hlt
    rw [List.getElem_ofFn] at hstep
    rw [← hstep, answers_getElem]
  have hview : ∀ i : Fin record.length,
      MessageDigest.parse (word ⟨i.val, lt_of_lt_of_le i.isLt hlen⟩) = recordTape record i := by
    intro i
    rw [hget i]
    rfl
  obtain ⟨j, hj⟩ := hcov
  refine ⟨⟨j.val, lt_of_lt_of_le j.isLt hlen⟩, fun tree => ?_⟩
  have hcovered := hj tree
  simp only [ForsDisclosureTape.disclosuresExcept, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and] at hcovered ⊢
  obtain ⟨k, ⟨hne, hinstance⟩, hleaf⟩ := hcovered
  refine ⟨⟨k.val, lt_of_lt_of_le k.isLt hlen⟩, ⟨?_, ?_⟩, ?_⟩
  · intro hsame
    refine hne (Fin.ext ?_)
    have hval : (k : Nat) = (j : Nat) := by simpa using hsame
    exact hval
  · rw [hview k, hview j]
    exact hinstance
  · rw [hview k, hview j]
    exact hleaf

/-! ## The bound on the run

Putting the pieces together: the recording is a uniform tape, and a covered recording is a
covered tape, so a run that records at most `trials` answers is covered with probability at
most `1 / 2 ^ 141 + trials / 2 ^ 128`. -/

/-- The padding block of a padded run has exactly the tape length. -/
theorem padded_length {α : Type} (keep : Bytes → Prop)
    (computation : OracleComp OracleWorld α) (state : RecordState) (trials : Nat)
    (result : (α × RecordState) × List HashOutput)
    (hmem : result ∈ support (paddedFrom keep computation state trials)) :
    result.2.length = trials := by
  rw [paddedFrom, mem_support_bind_iff] at hmem
  obtain ⟨inner, -, hrest⟩ := hmem
  rw [mem_support_bind_iff] at hrest
  obtain ⟨pad, hpad, hpure⟩ := hrest
  rw [support_pure, Set.mem_singleton_iff] at hpure
  rw [hpure]
  exact padding_length trials pad hpad

set_option maxHeartbeats 800000 in
/-- **The adaptive FORS coverage bound.** A run of the shared oracle that records at most
`trials` fresh `keep`-class answers ends holding a recorded digest whose fourteen FORS leaves
are all disclosed by the other recorded digests with probability at most
`1 / 2 ^ 141 + trials / 2 ^ 128` — one unit of `2 ^ -128` per recorded answer, with no
disclosure set and no set of inputs fixed in advance. -/
theorem prob_recordCovered_le {α : Type} (keep : Bytes → Prop)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec)
    (trials : Nat) (htrials : trials ≤ 5 * 2 ^ 62) :
    Pr[fun result : α × RecordState =>
        result.2.2.length ≤ trials ∧ RecordCovered result.2.2 |
      recordedRun keep computation cache] ≤
      (1 : ℝ≥0∞) / 2 ^ 141 + (trials : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  rw [recordedRun, ← probEvent_paddedFrom keep computation (cache, []) trials]
  refine le_trans (probEvent_mono ?_)
    (le_trans (prob_tape_event_le keep computation cache trials TapeCovered)
      (prob_tapeCovered_le trials htrials))
  rintro result hmem ⟨hlen, hcov⟩
  set whole : List HashOutput := answers result.1.2.2 ++ result.2 with hwhole
  have hpad : result.2.length = trials :=
    padded_length keep computation (cache, []) trials result hmem
  have hbig : trials ≤ whole.length := by
    rw [hwhole, List.length_append, hpad]
    omega
  have hofFn : List.ofFn (fun i : Fin trials => whole[i.val]'(lt_of_lt_of_le i.isLt hbig)) =
      whole.take trials := by
    refine List.ext_getElem (by simp [hbig]) fun n h₁ h₂ => ?_
    simp
  have hwholePrefix :
      List.ofFn (fun i : Fin trials => whole[i.val]'(lt_of_lt_of_le i.isLt hbig)) <+: whole := by
    rw [hofFn]
    exact List.take_prefix trials whole
  refine ⟨fun i => whole[i.val]'(lt_of_lt_of_le i.isLt hbig), ?_, hwholePrefix⟩
  refine tapeCovered_of_prefix result.1.2.2 _ ?_ hcov
  refine List.prefix_of_prefix_length_le (l₃ := whole) ?_ hwholePrefix ?_
  · rw [hwhole]
    exact List.prefix_append _ _
  · rw [List.length_ofFn, answers_length]
    exact hlen

/-- **The charge in the growth-budget form.** The tape length is supplied by the same
observable the class-split charges are stated against: a run whose cache grows at `keep`-class
inputs by at most `limit` records at most `limit` answers, so the coverage event costs
`1 / 2 ^ 141 + limit / 2 ^ 128` — one unit per `keep`-class query. -/
theorem prob_recordCovered_within_le {α : Type} (keep : Bytes → Prop)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec)
    (limit : Nat) (hlimit : limit ≤ 5 * 2 ^ 62) :
    Pr[fun result : α × RecordState =>
        ClassCharge.GrowthAtMostOn keep cache result.2.1 limit ∧ RecordCovered result.2.2 |
      recordedRun keep computation cache] ≤
      (1 : ℝ≥0∞) / 2 ^ 141 + (limit : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  refine le_trans (probEvent_mono ?_)
    (prob_recordCovered_le keep computation cache limit hlimit)
  rintro result hmem ⟨hgrowth, hcov⟩
  refine ⟨?_, hcov⟩
  have hbound :=
    record_length_le_growth keep computation (cache, []) limit result hmem hgrowth
  simpa using hbound

/-- **The bound transported to the plain run.** An event about the result and the final cache
that is always witnessed by a covered recording within the run's growth budget is charged at
the same rate. This is the shape a game supplies: a coverage event about the final cache is
witnessed by answers the run drew, and the charged query count bounds the growth. -/
theorem prob_romEvent_le {α : Type} (keep : Bytes → Prop)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec)
    (limit : Nat) (hlimit : limit ≤ 5 * 2 ^ 62)
    (event : α × QueryCache HashSpec → Prop)
    (hwitness : ∀ result ∈ support (recordedRun keep computation cache),
      event (result.1, result.2.1) →
        ClassCharge.GrowthAtMostOn keep cache result.2.1 limit ∧ RecordCovered result.2.2) :
    Pr[event | (simulateQ KeygenUniform.rom computation).run cache] ≤
      (1 : ℝ≥0∞) / 2 ^ 141 + (limit : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  rw [← probEvent_recordedRun keep computation cache event]
  exact le_trans (probEvent_mono hwitness)
    (prob_recordCovered_within_le keep computation cache limit hlimit)

end SlhDsaSecurity.DigestTape
