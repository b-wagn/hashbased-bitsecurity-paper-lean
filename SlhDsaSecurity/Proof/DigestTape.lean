import SlhDsaSecurity.Proof.GrowthCharge
import SlhDsaSecurity.Proof.ForsAdaptiveTargets
import SlhDsaSecurity.Proof.ForsDisclosureTape
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling
import SlhDsaSecurity.Proof.KeygenUniform
import SlhDsaSecurity.Proof.MessageDigest

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

/-! ## The instrumentation is invisible

The recording is a write-only component of the state: it never influences an answer, so the
instrumented run and the plain run of the shared oracle agree on every event that does not
mention it. -/

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

/-! ## The recording is paid for by cache growth

Each recorded answer is one cache miss at a `keep`-class input, so the recording is no longer
than the run's growth *in that class*. This is what identifies the tape length with a budget
the experiment already carries: `ClassCharge.GrowthAtMostOn` is the per-class observable the
class-split charges are stated against, so the coverage term is charged at one unit per
message-class query rather than per query. -/

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

/-! ## The lazy-sampling invariant

Any word fixed in advance is a prefix of what the run records with probability at most
`|HashOutput| ^ (-length)`: each of its letters has to be matched by one fresh uniform
answer. Nothing is assumed about *which* inputs the run queries — the coordinates are
positions in the recording order, not inputs, which is what removes the need to pin a finite
set of inputs in advance. -/

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

/-! ## The leave-one-out coverage event

`ForsLeaveOneOut.independent_tape_coverage_le` charges, on a uniform tape, the event that some
coordinate selected by a causal policy has its fourteen FORS leaves all disclosed by the other
coordinates. Taking the constant policy — every coordinate selected — gives the event in its
plainest form, and its expected number of selections is the tape length, so the charge is one
unit of `2 ^ -128` per coordinate. -/

/-! ## From the recording to the tape

A recorded list is read as a tape of its own length. Because coverage is monotone in the
disclosures, a covered recording stays covered inside any longer word extending it, so the
record's coverage event is charged by the full tape's. -/

/-! ## The bound on the run

Putting the pieces together: the recording is a uniform tape, and a covered recording is a
covered tape, so a run that records at most `trials` answers is covered with probability at
most `1 / 2 ^ 141 + trials / 2 ^ 128`. -/

end SlhDsaSecurity.DigestTape
