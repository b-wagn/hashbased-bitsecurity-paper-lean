import SlhDsaSecurity.Proof.PotentialCharge
import SlhDsaSecurity.Proof.LateCharge
import SlhDsaSecurity.Proof.FramingLeak

/-!
# The ordering defect's rate

`SplitWitness.Served.Late` is the one way the recorder's two classes can part from the final
cache's, and `PotentialCharge.prob_fired_le` is the charge for an event of that kind. This file
is the instantiation.

The gauge is the **target recording's length**, and the potential is the entries of that
recording that are not yet settled — the ones an answer still to be drawn can make disclosing.
A query the left test keeps raises neither number; a query the right test keeps raises both by
one; a query that settles entries pays for every unit standing at them and spends them all at
once. Nothing else moves either.

So the defect costs one unit of the rate per entry of the target recording, which is where the
budget has room for it. It is not charged at the message class: the signer's own digests are
recorded on the disclosing side, and they are paying elsewhere.

**The charge is stated over the tests, not over one choice of them.** `Served` below takes the
two recorder tests, a notion of an entry being *settled*, a notion of its being settled *by this
query*, and the rate, and asks of them only what the potential argument uses. The rate enters in
one place: a fresh answer makes a given recorded entry disclosing with probability at most the
rate. Nothing in the core mentions a key, a seed or a `PRF_msg` input, so the carrier's served
test will be another application of these lemmas rather than a rewrite of them; the key is named
once, by whoever instantiates, and the convention there is the walk's.

The signer instantiation follows: the left test is the cache's own `SK.prf` reading, settled
means the entry's message already has its `PRF_msg` entry, and the rate is `2 ^ -128` because
the answers that disclose a given entry are one fibre of a uniform draw.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.LateRate

open Security CacheAvailability SplitPrefix SplitWitness LateCharge ClassExpectation

/-! ## Counting a list by two tests -/

theorem length_filter_split {α : Type} (l : List α) (p q : α → Bool) :
    (l.filter (fun a => p a)).length =
      (l.filter (fun a => p a && q a)).length + (l.filter (fun a => p a && !q a)).length := by
  induction l with
  | nil => simp
  | cons head tail ih =>
    by_cases hp : p head
    · by_cases hq : q head <;> simp [hp, hq, ih] <;> omega
    · simp [hp, ih]

/-! ## Adding units of one rate -/

theorem rate_le (rate : ℝ≥0∞) {x y z w : Nat} (hle : x + y ≤ z + w) :
    ((x : Nat) : ℝ≥0∞) * rate + ((y : Nat) : ℝ≥0∞) * rate ≤
      ((z : Nat) : ℝ≥0∞) * rate + ((w : Nat) : ℝ≥0∞) * rate := by
  rw [show ((x : Nat) : ℝ≥0∞) * rate + ((y : Nat) : ℝ≥0∞) * rate =
      ((x + y : Nat) : ℝ≥0∞) * rate from by push_cast; ring,
    show ((z : Nat) : ℝ≥0∞) * rate + ((w : Nat) : ℝ≥0∞) * rate =
      ((z + w : Nat) : ℝ≥0∞) * rate from by push_cast; ring]
  exact mul_le_mul' (Nat.cast_le.mpr hle) le_rfl

theorem rate_le3 (rate : ℝ≥0∞) {x y z w v : Nat} (hle : x + y + z ≤ w + v) :
    ((x : Nat) : ℝ≥0∞) * rate + (((y : Nat) : ℝ≥0∞) * rate + ((z : Nat) : ℝ≥0∞) * rate) ≤
      ((w : Nat) : ℝ≥0∞) * rate + ((v : Nat) : ℝ≥0∞) * rate := by
  rw [show ((x : Nat) : ℝ≥0∞) * rate + (((y : Nat) : ℝ≥0∞) * rate + ((z : Nat) : ℝ≥0∞) * rate) =
      ((x + y + z : Nat) : ℝ≥0∞) * rate from by push_cast; ring,
    show ((w : Nat) : ℝ≥0∞) * rate + ((v : Nat) : ℝ≥0∞) * rate =
      ((w + v : Nat) : ℝ≥0∞) * rate from by push_cast; ring]
  exact mul_le_mul' (Nat.cast_le.mpr hle) le_rfl

/-! ## The charge over the tests

`left` and `right` are the recorder's two tests, `spent` says an entry's disclosure is already
decided, and `becomes` says this query decides it. The rate is whatever one entry costs. -/

namespace Served

/-- The event: some target-recorded entry is disclosing. -/
def Fired (left : Bytes → QueryCache HashSpec → Prop) (state : SplitState) : Prop :=
  ∃ entry ∈ state.2.2, left entry.1 state.1

/-- The gauge: how long the target recording is. -/
def gauge (state : SplitState) : Nat := state.2.2.length

open scoped Classical in
/-- The potential: the target-recorded entries that are not yet settled. -/
noncomputable def potential (spent : QueryCache HashSpec → Bytes → Prop)
    (state : SplitState) : Nat :=
  (state.2.2.filter (fun entry => decide (¬ spent state.1 entry.1))).length

/-- Where a fresh query takes the state. -/
noncomputable def stepOf (left right : Bytes → QueryCache HashSpec → Prop)
    (state : SplitState) (input : Bytes) (answer : HashOutput) : SplitState :=
  (state.1.cacheQuery input answer, appended left right input state answer)

theorem run_inl (left right : Bytes → QueryCache HashSpec → Prop) (coin : unifSpec.Domain)
    (state : SplitState) (step : OracleWorld.Range (Sum.inl coin) × SplitState)
    (hmem : step ∈ support (((recorder left right) (Sum.inl coin)).run state)) :
    step.2 = state := by
  rw [recorder_run_inl, mem_support_bind_iff] at hmem
  obtain ⟨value, -, hpure⟩ := hmem
  rw [support_pure, Set.mem_singleton_iff] at hpure
  exact congrArg Prod.snd hpure

theorem run_inl_mass (left right : Bytes → QueryCache HashSpec → Prop)
    (coin : unifSpec.Domain) (state : SplitState) :
    Pr[⊥ | ((recorder left right) (Sum.inl coin)).run state] = 0 := by
  rw [recorder_run_inl]
  simp

theorem run_inr_cached (left right : Bytes → QueryCache HashSpec → Prop) (input : Bytes)
    (state : SplitState) (answer : HashOutput) (hcached : state.1 input = some answer) :
    ((recorder left right) (Sum.inr input)).run state =
      (pure (answer, state) : ProbComp _) := by
  rw [recorder_run_inr, QueryImpl.withCaching_run_some _ hcached, pure_bind,
    appended_of_cached left right input state answer answer hcached]
  rfl

theorem run_inr_fresh (left right : Bytes → QueryCache HashSpec → Prop) (input : Bytes)
    (state : SplitState) (hfresh : state.1 input = none) :
    ((recorder left right) (Sum.inr input)).run state =
      (fun answer => (answer, stepOf left right state input answer)) <$>
        ($ᵗ HashOutput : ProbComp HashOutput) := by
  rw [recorder_run_inr, QueryImpl.withCaching_run_none _ hfresh]
  simp only [uniformSampleImpl, map_eq_bind_pure_comp, Function.comp_def,
    bind_assoc, pure_bind]
  rfl

theorem run_mass (left right : Bytes → QueryCache HashSpec → Prop) (β : Type)
    (inner : OracleComp OracleWorld β) (state : SplitState) :
    Pr[⊥ | (simulateQ (recorder left right) inner).run state] = 0 := by
  simp

theorem gauge_stepOf (left right : Bytes → QueryCache HashSpec → Prop) (state : SplitState)
    (input : Bytes) (answer : HashOutput) :
    gauge state ≤ gauge (stepOf left right state input answer) :=
  List.IsPrefix.length_le (right_prefix_appended left right input state answer)

theorem gauge_run (left right : Bytes → QueryCache HashSpec → Prop) (β : Type)
    (inner : OracleComp OracleWorld β) (state : SplitState) (result : β × SplitState)
    (hmem : result ∈ support ((simulateQ (recorder left right) inner).run state)) :
    gauge state ≤ gauge result.2 :=
  List.IsPrefix.length_le (record_prefix left right inner state result hmem).2

open scoped Classical in
/-- **The potential splits into what this query settles and what it leaves.** -/
theorem potential_split (spent : QueryCache HashSpec → Bytes → Prop)
    (becomes : QueryCache HashSpec → Bytes → Bytes → Prop)
    (hbecomes : ∀ (cache : QueryCache HashSpec) (input entry : Bytes),
      spent cache entry → becomes cache input entry)
    (cache : QueryCache HashSpec) (input : Bytes) (record : List (Bytes × HashOutput)) :
    (record.filter (fun entry => decide (¬ spent cache entry.1))).length =
      (record.filter (fun entry => decide (¬ spent cache entry.1 ∧
          becomes cache input entry.1))).length +
        (record.filter (fun entry => decide (¬ becomes cache input entry.1))).length := by
  classical
  rw [length_filter_split record (fun entry => decide (¬ spent cache entry.1))
    (fun entry => decide (becomes cache input entry.1))]
  congr 1
  · exact congrArg List.length (List.filter_congr fun entry _ => by simp)
  · refine congrArg List.length (List.filter_congr fun entry _ => ?_)
    by_cases hbecame : becomes cache input entry.1
    · simp [hbecame]
    · have hspent : ¬ spent cache entry.1 := fun hspent =>
        hbecame (hbecomes cache input entry.1 hspent)
      simp [hbecame, hspent]

open scoped Classical in
/-- The potential after the query, read without the answer. -/
theorem potential_stepOf (left right : Bytes → QueryCache HashSpec → Prop)
    (spent : QueryCache HashSpec → Bytes → Prop)
    (becomes : QueryCache HashSpec → Bytes → Bytes → Prop)
    (hsettles : ∀ (cache : QueryCache HashSpec) (input entry : Bytes) (answer : HashOutput),
      cache input = none →
        (spent (cache.cacheQuery input answer) entry ↔ becomes cache input entry))
    (state : SplitState) (input : Bytes) (answer : HashOutput)
    (hfresh : state.1 input = none) :
    potential spent (stepOf left right state input answer) =
      ((appended left right input state answer).2.filter
        (fun entry => decide (¬ becomes state.1 input entry.1))).length := by
  classical
  refine congrArg List.length (List.filter_congr fun entry _ => ?_)
  rw [show (stepOf left right state input answer).1 = state.1.cacheQuery input answer from rfl]
  by_cases hbecame : becomes state.1 input entry.1
  · have hspent : spent (state.1.cacheQuery input answer) entry.1 :=
      (hsettles state.1 input entry.1 answer hfresh).mpr hbecame
    simp [hbecame, hspent]
  · have hspent : ¬ spent (state.1.cacheQuery input answer) entry.1 := fun hspent =>
      hbecame ((hsettles state.1 input entry.1 answer hfresh).mp hspent)
    simp [hbecame, hspent]

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The step hypothesis of the potential charge, for this event.**

A query the left test keeps adds nothing to the target recording, so the gauge stands and the
potential only loses what the query settles. A query the right test keeps adds one entry, which
costs one unit of the rate — the new entry is not disclosing when it is filed, by `hexcludes`,
so `hentry` bounds the chance this very answer discloses it. Everything else is the record's own
loss, bounded by `hrecord`. -/
theorem step_bound (left right : Bytes → QueryCache HashSpec → Prop)
    (spent : QueryCache HashSpec → Bytes → Prop)
    (becomes : QueryCache HashSpec → Bytes → Bytes → Prop) (rate : ℝ≥0∞)
    (hexcludes : ∀ (input : Bytes) (cache : QueryCache HashSpec),
      right input cache → ¬ left input cache)
    (hbecomes : ∀ (cache : QueryCache HashSpec) (input entry : Bytes),
      spent cache entry → becomes cache input entry)
    (hsettles : ∀ (cache : QueryCache HashSpec) (input entry : Bytes) (answer : HashOutput),
      cache input = none →
        (spent (cache.cacheQuery input answer) entry ↔ becomes cache input entry))
    (hleftSpent : ∀ (cache : QueryCache HashSpec) (entry : Bytes),
      left entry cache → spent cache entry)
    (hrecord : ∀ (cache : QueryCache HashSpec) (input : Bytes)
        (record : List (Bytes × HashOutput)), cache input = none →
      (∀ entry ∈ record, ¬ left entry.1 cache) →
        Pr[fun answer : HashOutput => ∃ entry ∈ record,
            left entry.1 (cache.cacheQuery input answer) |
          ($ᵗ HashOutput : ProbComp HashOutput)] ≤
          (((record.filter (fun entry => decide (¬ spent cache entry.1 ∧
              becomes cache input entry.1))).length : Nat) : ℝ≥0∞) * rate)
    (hentry : ∀ (cache : QueryCache HashSpec) (input entry : Bytes),
      ¬ left entry cache →
        Pr[fun answer : HashOutput => left entry (cache.cacheQuery input answer) |
          ($ᵗ HashOutput : ProbComp HashOutput)] ≤ rate)
    (state : SplitState) (input : Bytes) (hfresh : state.1 input = none)
    (hnotfired : ¬ Fired left state) :
    ∃ bound after : Nat,
      (∀ answer : HashOutput, ¬ Fired left (stepOf left right state input answer) →
          potential spent (stepOf left right state input answer) ≤ bound) ∧
        (∀ answer : HashOutput, gauge (stepOf left right state input answer) = after) ∧
          Pr[fun answer : HashOutput =>
              Fired left (stepOf left right state input answer) |
            ($ᵗ HashOutput : ProbComp HashOutput)] + ((bound : Nat) : ℝ≥0∞) * rate ≤
            ((potential spent state : Nat) : ℝ≥0∞) * rate +
              ((after - gauge state : Nat) : ℝ≥0∞) * rate := by
  classical
  have hnot : ∀ entry ∈ state.2.2, ¬ left entry.1 state.1 :=
    fun entry hentryMem hleft => hnotfired ⟨entry, hentryMem, hleft⟩
  have hpot : potential spent state =
      (state.2.2.filter (fun entry => decide (¬ spent state.1 entry.1 ∧
          becomes state.1 input entry.1))).length +
        (state.2.2.filter (fun entry =>
          decide (¬ becomes state.1 input entry.1))).length :=
    potential_split spent becomes hbecomes state.1 input state.2.2
  have hold : Pr[fun answer : HashOutput => ∃ entry ∈ state.2.2,
        left entry.1 (state.1.cacheQuery input answer) |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤
      (((state.2.2.filter (fun entry => decide (¬ spent state.1 entry.1 ∧
          becomes state.1 input entry.1))).length : Nat) : ℝ≥0∞) * rate :=
    hrecord state.1 input state.2.2 hfresh hnot
  by_cases hleft : left input state.1
  · refine ⟨(state.2.2.filter (fun entry =>
      decide (¬ becomes state.1 input entry.1))).length, gauge state,
      fun answer _ => ?_, fun answer => ?_, ?_⟩
    · rw [potential_stepOf left right spent becomes hsettles state input answer hfresh,
        appended_of_left left right input state answer hfresh hleft]
    · show ((appended left right input state answer).2).length = state.2.2.length
      rw [appended_of_left left right input state answer hfresh hleft]
    · rw [hpot]
      refine le_trans (add_le_add (le_trans (probEvent_mono fun answer _ hfired => ?_) hold)
        le_rfl) (rate_le rate (by omega))
      obtain ⟨entry, hentryMem, hleftEntry⟩ := hfired
      refine ⟨entry, ?_, hleftEntry⟩
      rwa [show (stepOf left right state input answer).2.2 =
        (appended left right input state answer).2 from rfl,
        appended_of_left left right input state answer hfresh hleft] at hentryMem
  · by_cases hright : right input state.1
    · have hshape : ∀ answer : HashOutput,
          (appended left right input state answer).2 = state.2.2 ++ [(input, answer)] :=
        fun answer => by
          rw [appended_of_right left right input state answer hfresh hleft hright]
      have hsplit : ∀ answer : HashOutput,
          Pr[fun answer : HashOutput =>
              Fired left (stepOf left right state input answer) |
            ($ᵗ HashOutput : ProbComp HashOutput)] ≤
            Pr[fun answer : HashOutput => ∃ entry ∈ state.2.2,
                left entry.1 (state.1.cacheQuery input answer) |
              ($ᵗ HashOutput : ProbComp HashOutput)] +
              Pr[fun answer : HashOutput => left input (state.1.cacheQuery input answer) |
                ($ᵗ HashOutput : ProbComp HashOutput)] := fun _ => by
        refine le_trans (probEvent_mono (q := fun answer : HashOutput =>
          (∃ entry ∈ state.2.2, left entry.1 (state.1.cacheQuery input answer)) ∨
          left input (state.1.cacheQuery input answer))
          fun answer _ hfired => ?_) (probEvent_or_le _ _ _)
        obtain ⟨entry, hentryMem, hleftEntry⟩ := hfired
        rw [show (stepOf left right state input answer).2.2 =
          (appended left right input state answer).2 from rfl, hshape answer] at hentryMem
        rcases List.mem_append.mp hentryMem with hmem | hmem
        · exact Or.inl ⟨entry, hmem, hleftEntry⟩
        · rw [List.mem_singleton.mp hmem] at hleftEntry
          exact Or.inr hleftEntry
      by_cases hself : becomes state.1 input input
      · refine ⟨(state.2.2.filter (fun entry =>
          decide (¬ becomes state.1 input entry.1))).length, gauge state + 1,
          fun answer _ => ?_, fun answer => ?_, ?_⟩
        · rw [potential_stepOf left right spent becomes hsettles state input answer hfresh,
            hshape answer, List.filter_append]
          simp [hself]
        · show ((appended left right input state answer).2).length = state.2.2.length + 1
          rw [hshape answer]
          simp
        · have hone : Pr[fun answer : HashOutput =>
              left input (state.1.cacheQuery input answer) |
            ($ᵗ HashOutput : ProbComp HashOutput)] ≤ ((1 : Nat) : ℝ≥0∞) * rate := by
            rw [Nat.cast_one, one_mul]
            exact hentry state.1 input input (hexcludes input state.1 hright)
          rw [hpot]
          refine le_trans (add_le_add (le_trans (hsplit default)
            (add_le_add hold hone)) le_rfl) ?_
          rw [add_assoc]
          exact rate_le3 rate (by omega)
      · refine ⟨(state.2.2.filter (fun entry =>
          decide (¬ becomes state.1 input entry.1))).length + 1, gauge state + 1,
          fun answer _ => ?_, fun answer => ?_, ?_⟩
        · rw [potential_stepOf left right spent becomes hsettles state input answer hfresh,
            hshape answer, List.filter_append]
          simp [hself]
        · show ((appended left right input state answer).2).length = state.2.2.length + 1
          rw [hshape answer]
          simp
        · have hzero : Pr[fun answer : HashOutput =>
              left input (state.1.cacheQuery input answer) |
            ($ᵗ HashOutput : ProbComp HashOutput)] = 0 :=
            probEvent_eq_zero fun answer _ hleftSelf => hself
              ((hsettles state.1 input input answer hfresh).mp
                (hleftSpent (state.1.cacheQuery input answer) input hleftSelf))
          rw [hpot]
          refine le_trans (add_le_add (le_trans (hsplit default)
            (add_le_add hold (le_of_eq hzero))) le_rfl) ?_
          rw [add_zero]
          exact rate_le rate (by omega)
    · refine ⟨(state.2.2.filter (fun entry =>
        decide (¬ becomes state.1 input entry.1))).length, gauge state,
        fun answer _ => ?_, fun answer => ?_, ?_⟩
      · rw [potential_stepOf left right spent becomes hsettles state input answer hfresh,
          appended_of_neither left right input state answer hleft hright]
      · show ((appended left right input state answer).2).length = state.2.2.length
        rw [appended_of_neither left right input state answer hleft hright]
      · rw [hpot]
        refine le_trans (add_le_add (le_trans (probEvent_mono fun answer _ hfired => ?_) hold)
          le_rfl) (rate_le rate (by omega))
        obtain ⟨entry, hentryMem, hleftEntry⟩ := hfired
        refine ⟨entry, ?_, hleftEntry⟩
        rwa [show (stepOf left right state input answer).2.2 =
          (appended left right input state answer).2 from rfl,
          appended_of_neither left right input state answer hleft hright] at hentryMem

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The ordering defect's rate, at the tests.** The run holds a target-recorded entry that it
later made disclosing with probability at most one unit of the rate per entry of the target
recording. -/
theorem prob_fired_le (left right : Bytes → QueryCache HashSpec → Prop)
    (spent : QueryCache HashSpec → Bytes → Prop)
    (becomes : QueryCache HashSpec → Bytes → Bytes → Prop) (rate : ℝ≥0∞)
    (hexcludes : ∀ (input : Bytes) (cache : QueryCache HashSpec),
      right input cache → ¬ left input cache)
    (hbecomes : ∀ (cache : QueryCache HashSpec) (input entry : Bytes),
      spent cache entry → becomes cache input entry)
    (hsettles : ∀ (cache : QueryCache HashSpec) (input entry : Bytes) (answer : HashOutput),
      cache input = none →
        (spent (cache.cacheQuery input answer) entry ↔ becomes cache input entry))
    (hleftSpent : ∀ (cache : QueryCache HashSpec) (entry : Bytes),
      left entry cache → spent cache entry)
    (hrecord : ∀ (cache : QueryCache HashSpec) (input : Bytes)
        (record : List (Bytes × HashOutput)), cache input = none →
      (∀ entry ∈ record, ¬ left entry.1 cache) →
        Pr[fun answer : HashOutput => ∃ entry ∈ record,
            left entry.1 (cache.cacheQuery input answer) |
          ($ᵗ HashOutput : ProbComp HashOutput)] ≤
          (((record.filter (fun entry => decide (¬ spent cache entry.1 ∧
              becomes cache input entry.1))).length : Nat) : ℝ≥0∞) * rate)
    (hentry : ∀ (cache : QueryCache HashSpec) (input entry : Bytes),
      ¬ left entry cache →
        Pr[fun answer : HashOutput => left entry (cache.cacheQuery input answer) |
          ($ᵗ HashOutput : ProbComp HashOutput)] ≤ rate)
    (computation : OracleComp OracleWorld (Outcome × Nat)) (cache : QueryCache HashSpec) :
    Pr[fun result : (Outcome × Nat) × SplitState => Fired left result.2 |
        (simulateQ (recorder left right) computation).run (cache, [], [])] ≤
      expected ((simulateQ (recorder left right) computation).run (cache, [], []))
        (fun result => result.2.2.2.length) * rate := by
  classical
  have hmain := PotentialCharge.prob_fired_le (recorder left right)
    (fun state => state.1) (stepOf left right)
    (run_inl left right) (run_inl_mass left right) (run_inr_cached left right)
    (run_inr_fresh left right) (run_mass left right)
    (Fired left) (potential spent) gauge rate
    (gauge_stepOf left right) (gauge_run left right)
    (fun state input hcache hnotfired =>
      step_bound left right spent becomes rate hexcludes hbecomes hsettles hleftSpent hrecord
        hentry state input hcache hnotfired)
    computation (cache, [], [])
    (by rintro ⟨entry, hentryMem, -⟩; simp at hentryMem)
  simpa [potential, gauge] using hmain

end Served

/-! ## The signer instantiation

The test the recorder can run today reads the cache alone, an entry is settled once its own
message has its `PRF_msg` entry, and the rate is `2 ^ -128` because the answers that disclose a
given entry all have the same truncation. -/

/-- The rate the defect is charged at. -/
noncomputable def rate : ℝ≥0∞ := (1 : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)

/-- The event: some target-recorded digest is disclosing. -/
def Fired (prfSeed : Digest) (pk : PublicKey) (state : SplitState) : Prop :=
  Served.Fired (disclosingKeep prfSeed pk) state

/-- `LateDisclosure` is the event, read at the state. -/
theorem fired_iff_lateDisclosure (prfSeed : Digest) (pk : PublicKey)
    (result : (Outcome × Nat) × SplitState) :
    Fired prfSeed pk result.2 ↔ LateDisclosure prfSeed pk result := Iff.rfl

/-- A digest already settled stays settled when one more query is answered. -/
theorem becomesSpent_of_spent (prfSeed : Digest) (pk : PublicKey) (cache : QueryCache HashSpec)
    (input entry : Bytes) (hspent : Spent prfSeed pk cache entry) :
    BecomesSpent prfSeed pk cache input entry := by
  obtain ⟨message, randomizer, hentry, hpresent⟩ := hspent
  exact ⟨message, randomizer, hentry, Or.inl hpresent⟩

set_option maxHeartbeats 1000000 in
/-- **The ordering defect's rate.** The run holds a target-recorded digest that it later made
disclosing with probability at most one unit of `2 ^ -128` per entry of the target recording.

The count is the recording's own length, read off each run: the signer's digests are not in it,
being recorded on the disclosing side, so this is not charged at the message class. -/
theorem prob_lateDisclosure_le (prfSeed : Digest) (pk : PublicKey)
    (computation : OracleComp OracleWorld (Outcome × Nat)) (cache : QueryCache HashSpec) :
    Pr[fun result : (Outcome × Nat) × SplitState => LateDisclosure prfSeed pk result |
        (simulateQ (recorder (disclosingKeep prfSeed pk) (targetKeep prfSeed pk))
          computation).run (cache, [], [])] ≤
      expected ((simulateQ (recorder (disclosingKeep prfSeed pk) (targetKeep prfSeed pk))
          computation).run (cache, [], []))
        (fun result => result.2.2.2.length) * rate :=
  Served.prob_fired_le (disclosingKeep prfSeed pk) (targetKeep prfSeed pk)
    (Spent prfSeed pk) (BecomesSpent prfSeed pk) rate
    (fun _ _ hkeep => hkeep.2)
    (fun cache input entry hspent => becomesSpent_of_spent prfSeed pk cache input entry hspent)
    (fun cache input entry answer hfresh =>
      spent_cacheQuery_iff prfSeed pk cache input entry answer hfresh)
    (fun cache entry hleft => spent_of_signerRandomised prfSeed pk cache entry hleft)
    (fun cache input record hfresh hnot =>
      prob_record_fires_le prfSeed pk cache input record hfresh hnot)
    (fun cache input entry hnot => prob_entry_fires_le prfSeed pk cache input entry hnot)
    computation cache

/-! ## The target recording is not the adversary's alone

The count above is the target recording's length, and the budget wants to read that as the
adversary's own message-class queries — the signer's digests being on the disclosing side,
because the signer asks `PRF_msg` before it asks `H_msg`. That reading is right for the
*digest* a served request makes. It is not right for the request's own `PRF_msg` query.

`FramingLeak.randomizerInput_eq_messageInput` is an unconditional identity of the FIPS 205
byte formats: `PRF_msg(SK.prf, PK.seed, PK.root ‖ m)` *is* `H_msg(SK.prf, PK.seed, PK.root, m)`.
So on a request framed as `PK.root ‖ m` — a legal request whenever `PK.root` begins with a zero
byte, by `FramingLeak.exists_legal_request`, which `FramingOverlap.keygen_zero_probability`
puts at exactly `1 / 256` — the signer's own `PRF_msg` query is a message-class input. It is
not signer-randomised when it is made unless the cache already holds the digest its own answer
would randomise, so the recorder files it on the target side.

The lemma below is that fact, stated at the recorder: it is not an obstruction to the charge
above, which counts whatever the target recording holds, but it is an obstruction to reading
that count as the adversary's queries alone. -/

/-- **A served request's own `PRF_msg` query is kept out of the target recording.** Without the
narrowing it would be filed there: it is a message input, by the format identity, and it is not
signer-randomised when it is made. The `PRF_msg` clause is what excludes it. -/
theorem not_targetKeep_signer_randomizerInput (prfSeed : Digest) (pk : PublicKey)
    (cache : QueryCache HashSpec) (message : Bytes) :
    ¬ targetKeep prfSeed pk
      (Hashing.randomizerInput prfSeed pk.seed (bytesBE n pk.root ++ message)) cache :=
  fun hkeep => hkeep.1.2 ⟨pk.seed, bytesBE n pk.root ++ message, rfl⟩

/-- The same input, read as the digest input it also is. -/
theorem signer_randomizerInput_isMessageInput (prfSeed : Digest) (pk : PublicKey)
    (message : Bytes) :
    CombinedCharge.IsMessageInput pk
      (Hashing.randomizerInput prfSeed pk.seed (bytesBE n pk.root ++ message)) :=
  ⟨prfSeed, message, FramingLeak.randomizerInput_eq_messageInput prfSeed pk message⟩

end SlhDsaSecurity.LateRate
