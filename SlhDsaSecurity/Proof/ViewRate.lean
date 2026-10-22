import SlhDsaSecurity.Proof.LateRate

/-!
# The ordering defect's step bound, at a view

`LateRate.Served.step_bound` is the step hypothesis of the potential charge for a recorder whose
two tests read the **cache**. This is the same bound for a recorder whose tests read a
`RecorderView.CacheView` — the carrier, say — and it is the last induction-free piece between the
composition and `hordering`.

**Why it has to be rewritten rather than reused.** `RecorderView.appendedOf` reads its two tests
at a *view*; `SplitPrefix.appended` reads them at a cache. There is no choice of cache-level tests
that recovers a view, so the carrier's step does not project to `LateRate.Served.stepOf` and the
proof has to be taken at the view. Everything *under* it is reused: `potential_split`, `rate_le`
and `rate_le3` are about caches and lists and are quoted from `LateRate` unchanged, and so are
all five of the probability facts the signer instantiation already proves.

**The tests are read at the notice, not at the state.** `appendedOf` is applied to
`CacheView.onQuery state.1 input`, so that is where `leftKeep` and `rightKeep` are consulted —
which is the rule the whole file family keeps: *a filing test is read at the state the query is
made from*, and after the notice is that state. The freshness guard is unaffected, because
`cacheOf_onQuery` says the notice does not move the cache.

**What fires, by contrast, is read at the cache.** `Fired` is `endKeep` at `cacheOf state.1`, and
that is deliberate: what files may be a flag that is down again later, what fires has to be
monotone and readable at the end. The two are different objects here, and the one place that
costs anything is `hexcludes` — see below.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.ViewRate

open Security SplitPrefix RecorderView LateRate

variable {σ : Type} [CacheView σ]

/-! ## The three readings, at a view -/

/-- The event: some target-recorded entry is disclosing at the end, read at the view's cache. -/
def Fired (endKeep : Bytes → QueryCache HashSpec → Prop) (state : StateOf σ) : Prop :=
  ∃ entry ∈ state.2.2, endKeep entry.1 (CacheView.cacheOf state.1)

/-- The gauge: how long the target recording is. -/
def gauge (state : StateOf σ) : Nat := state.2.2.length

open scoped Classical in
/-- The potential: the target-recorded entries that are not yet settled. -/
noncomputable def potential (spent : QueryCache HashSpec → Bytes → Prop)
    (state : StateOf σ) : Nat :=
  (state.2.2.filter (fun entry =>
    decide (¬ spent (CacheView.cacheOf state.1) entry.1))).length

/-- Where a fresh query takes the state: the notice first, then the answer, with whichever
recording the two tests name gaining this query's entry. -/
noncomputable def stepOf (leftKeep rightKeep : Bytes → σ → Prop) (state : StateOf σ)
    (input : Bytes) (answer : HashOutput) : StateOf σ :=
  (CacheView.update (CacheView.onQuery state.1 input) input answer,
    appendedOf leftKeep rightKeep input (CacheView.onQuery state.1 input, state.2) answer)

theorem cacheOf_stepOf (leftKeep rightKeep : Bytes → σ → Prop) (state : StateOf σ)
    (input : Bytes) (answer : HashOutput) :
    CacheView.cacheOf (stepOf leftKeep rightKeep state input answer).1 =
      (CacheView.cacheOf state.1).cacheQuery input answer := by
  rw [stepOf]
  show CacheView.cacheOf
      (CacheView.update (CacheView.onQuery state.1 input) input answer) = _
  rw [CacheView.cache_update, cacheOf_onQuery]

theorem right_stepOf (leftKeep rightKeep : Bytes → σ → Prop) (state : StateOf σ)
    (input : Bytes) (answer : HashOutput) :
    (stepOf leftKeep rightKeep state input answer).2.2 =
      (appendedOf leftKeep rightKeep input
        (CacheView.onQuery state.1 input, state.2) answer).2 := rfl

/-- **A fresh step never shortens the target recording.** -/
theorem gauge_stepOf (leftKeep rightKeep : Bytes → σ → Prop) (state : StateOf σ)
    (input : Bytes) (answer : HashOutput) :
    gauge state ≤ gauge (stepOf leftKeep rightKeep state input answer) := by
  refine List.IsPrefix.length_le ?_
  rw [right_stepOf]
  exact right_prefix_appendedOf leftKeep rightKeep input
    (CacheView.onQuery state.1 input, state.2) answer

/-! ## The potential after the step, read without the answer

The answer-independence is the whole reason the charge's induction closes, and it comes from
`hsettles`: once this query is answered, an entry is settled exactly when this query was the one
that would settle it, which does not mention the answer. -/

open scoped Classical in
theorem potential_stepOf (leftKeep rightKeep : Bytes → σ → Prop)
    (spent : QueryCache HashSpec → Bytes → Prop)
    (becomes : QueryCache HashSpec → Bytes → Bytes → Prop)
    (hsettles : ∀ (cache : QueryCache HashSpec) (input entry : Bytes) (answer : HashOutput),
      cache input = none →
        (spent (cache.cacheQuery input answer) entry ↔ becomes cache input entry))
    (state : StateOf σ) (input : Bytes) (answer : HashOutput)
    (hfresh : CacheView.cacheOf state.1 input = none) :
    potential spent (stepOf leftKeep rightKeep state input answer) =
      ((appendedOf leftKeep rightKeep input
          (CacheView.onQuery state.1 input, state.2) answer).2.filter
        (fun entry =>
          decide (¬ becomes (CacheView.cacheOf state.1) input entry.1))).length := by
  classical
  rw [potential, right_stepOf, cacheOf_stepOf]
  refine congrArg List.length (List.filter_congr fun entry _ => ?_)
  by_cases hbecame : becomes (CacheView.cacheOf state.1) input entry.1
  · have hspent : spent ((CacheView.cacheOf state.1).cacheQuery input answer) entry.1 :=
      (hsettles (CacheView.cacheOf state.1) input entry.1 answer hfresh).mpr hbecame
    simp [hbecame, hspent]
  · have hspent : ¬ spent ((CacheView.cacheOf state.1).cacheQuery input answer) entry.1 :=
      fun hspent =>
        hbecame ((hsettles (CacheView.cacheOf state.1) input entry.1 answer hfresh).mp hspent)
    simp [hbecame, hspent]

/-! ## The step bound

The three cases are the three things a fresh query can do to the recordings: file on the left,
file on the right, file nowhere. Only the middle one costs a unit of the rate, and it costs one
because the entry it files has not fired when it is filed — which is `hexcludes`.

**`hexcludes` is the one hypothesis that is not free at a view.** On the cache route the target
test *is* `narrow ∧ ¬ endKeep`, so the exclusion is a projection. At a view the right test may
exclude something else — the carrier's excludes the serving flag, which is a different object
from the cache-side disclosure — and then an entry could be filed already fired, at probability
one, with no rate to pay for it. So the hypothesis is stated here and the instantiation has to
mean it: the test the charge is read at must exclude what fires.
-/

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The step hypothesis of the potential charge, at a view.** -/
theorem step_bound (leftKeep rightKeep : Bytes → σ → Prop)
    (endKeep : Bytes → QueryCache HashSpec → Prop)
    (spent : QueryCache HashSpec → Bytes → Prop)
    (becomes : QueryCache HashSpec → Bytes → Bytes → Prop) (rate : ℝ≥0∞)
    (hexcludes : ∀ (input : Bytes) (view : σ),
      CacheView.cacheOf view input = none → rightKeep input view →
        ¬ endKeep input (CacheView.cacheOf view))
    (hbecomes : ∀ (cache : QueryCache HashSpec) (input entry : Bytes),
      spent cache entry → becomes cache input entry)
    (hsettles : ∀ (cache : QueryCache HashSpec) (input entry : Bytes) (answer : HashOutput),
      cache input = none →
        (spent (cache.cacheQuery input answer) entry ↔ becomes cache input entry))
    (hleftSpent : ∀ (cache : QueryCache HashSpec) (entry : Bytes),
      endKeep entry cache → spent cache entry)
    (hrecord : ∀ (cache : QueryCache HashSpec) (input : Bytes)
        (record : List (Bytes × HashOutput)), cache input = none →
      (∀ entry ∈ record, ¬ endKeep entry.1 cache) →
        Pr[fun answer : HashOutput => ∃ entry ∈ record,
            endKeep entry.1 (cache.cacheQuery input answer) |
          ($ᵗ HashOutput : ProbComp HashOutput)] ≤
          (((record.filter (fun entry => decide (¬ spent cache entry.1 ∧
              becomes cache input entry.1))).length : Nat) : ℝ≥0∞) * rate)
    (hentry : ∀ (cache : QueryCache HashSpec) (input entry : Bytes),
      ¬ endKeep entry cache →
        Pr[fun answer : HashOutput => endKeep entry (cache.cacheQuery input answer) |
          ($ᵗ HashOutput : ProbComp HashOutput)] ≤ rate)
    (state : StateOf σ) (input : Bytes)
    (hfresh : CacheView.cacheOf state.1 input = none)
    (hnotfired : ¬ Fired endKeep state) :
    ∃ bound after : Nat,
      (∀ answer : HashOutput, ¬ Fired endKeep (stepOf leftKeep rightKeep state input answer) →
          potential spent (stepOf leftKeep rightKeep state input answer) ≤ bound) ∧
        (∀ answer : HashOutput, gauge (stepOf leftKeep rightKeep state input answer) = after) ∧
          Pr[fun answer : HashOutput =>
              Fired endKeep (stepOf leftKeep rightKeep state input answer) |
            ($ᵗ HashOutput : ProbComp HashOutput)] + ((bound : Nat) : ℝ≥0∞) * rate ≤
            ((potential spent state : Nat) : ℝ≥0∞) * rate +
              ((after - gauge state : Nat) : ℝ≥0∞) * rate := by
  classical
  -- The cache is the same before and after the notice, so freshness reads the same at both.
  have hnoticeFresh : CacheView.cacheOf (CacheView.onQuery state.1 input) input = none := by
    rw [cacheOf_onQuery]; exact hfresh
  have hnoticeCache : CacheView.cacheOf (CacheView.onQuery state.1 input) =
      CacheView.cacheOf state.1 := cacheOf_onQuery state.1 input
  have hnot : ∀ entry ∈ state.2.2, ¬ endKeep entry.1 (CacheView.cacheOf state.1) :=
    fun entry hentryMem hleft => hnotfired ⟨entry, hentryMem, hleft⟩
  have hpot : potential spent state =
      (state.2.2.filter (fun entry => decide (¬ spent (CacheView.cacheOf state.1) entry.1 ∧
          becomes (CacheView.cacheOf state.1) input entry.1))).length +
        (state.2.2.filter (fun entry =>
          decide (¬ becomes (CacheView.cacheOf state.1) input entry.1))).length :=
    Served.potential_split spent becomes hbecomes (CacheView.cacheOf state.1) input state.2.2
  have hold : Pr[fun answer : HashOutput => ∃ entry ∈ state.2.2,
        endKeep entry.1 ((CacheView.cacheOf state.1).cacheQuery input answer) |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤
      (((state.2.2.filter (fun entry => decide (¬ spent (CacheView.cacheOf state.1) entry.1 ∧
          becomes (CacheView.cacheOf state.1) input entry.1))).length : Nat) : ℝ≥0∞) * rate :=
    hrecord (CacheView.cacheOf state.1) input state.2.2 hfresh hnot
  by_cases hleft : leftKeep input (CacheView.onQuery state.1 input)
  · refine ⟨(state.2.2.filter (fun entry =>
      decide (¬ becomes (CacheView.cacheOf state.1) input entry.1))).length, gauge state,
      fun answer _ => ?_, fun answer => ?_, ?_⟩
    · rw [potential_stepOf leftKeep rightKeep spent becomes hsettles state input answer hfresh,
        appendedOf_of_left leftKeep rightKeep input
          (CacheView.onQuery state.1 input, state.2) answer hnoticeFresh hleft]
    · show (appendedOf leftKeep rightKeep input
        (CacheView.onQuery state.1 input, state.2) answer).2.length = state.2.2.length
      rw [appendedOf_of_left leftKeep rightKeep input
        (CacheView.onQuery state.1 input, state.2) answer hnoticeFresh hleft]
    · rw [hpot]
      refine le_trans (add_le_add (le_trans (probEvent_mono fun answer _ hfired => ?_) hold)
        le_rfl) (rate_le rate (by omega))
      obtain ⟨entry, hentryMem, hleftEntry⟩ := hfired
      rw [cacheOf_stepOf] at hleftEntry
      refine ⟨entry, ?_, hleftEntry⟩
      rwa [right_stepOf, appendedOf_of_left leftKeep rightKeep input
        (CacheView.onQuery state.1 input, state.2) answer hnoticeFresh hleft] at hentryMem
  · by_cases hright : rightKeep input (CacheView.onQuery state.1 input)
    · have hshape : ∀ answer : HashOutput,
          (appendedOf leftKeep rightKeep input
            (CacheView.onQuery state.1 input, state.2) answer).2 =
              state.2.2 ++ [(input, answer)] :=
        fun answer => by
          rw [appendedOf_of_right leftKeep rightKeep input
            (CacheView.onQuery state.1 input, state.2) answer hnoticeFresh hleft hright]
      have hsplit : ∀ answer : HashOutput,
          Pr[fun answer : HashOutput =>
              Fired endKeep (stepOf leftKeep rightKeep state input answer) |
            ($ᵗ HashOutput : ProbComp HashOutput)] ≤
            Pr[fun answer : HashOutput => ∃ entry ∈ state.2.2,
                endKeep entry.1 ((CacheView.cacheOf state.1).cacheQuery input answer) |
              ($ᵗ HashOutput : ProbComp HashOutput)] +
              Pr[fun answer : HashOutput =>
                  endKeep input ((CacheView.cacheOf state.1).cacheQuery input answer) |
                ($ᵗ HashOutput : ProbComp HashOutput)] := fun _ => by
        refine le_trans (probEvent_mono (q := fun answer : HashOutput =>
          (∃ entry ∈ state.2.2,
              endKeep entry.1 ((CacheView.cacheOf state.1).cacheQuery input answer)) ∨
            endKeep input ((CacheView.cacheOf state.1).cacheQuery input answer))
          fun answer _ hfired => ?_) (probEvent_or_le _ _ _)
        obtain ⟨entry, hentryMem, hleftEntry⟩ := hfired
        rw [cacheOf_stepOf] at hleftEntry
        rw [right_stepOf, hshape answer] at hentryMem
        rcases List.mem_append.mp hentryMem with hmem | hmem
        · exact Or.inl ⟨entry, hmem, hleftEntry⟩
        · rw [List.mem_singleton.mp hmem] at hleftEntry
          exact Or.inr hleftEntry
      by_cases hself : becomes (CacheView.cacheOf state.1) input input
      · refine ⟨(state.2.2.filter (fun entry =>
          decide (¬ becomes (CacheView.cacheOf state.1) input entry.1))).length, gauge state + 1,
          fun answer _ => ?_, fun answer => ?_, ?_⟩
        · rw [potential_stepOf leftKeep rightKeep spent becomes hsettles state input answer
            hfresh, hshape answer, List.filter_append]
          simp [hself]
        · show (appendedOf leftKeep rightKeep input
            (CacheView.onQuery state.1 input, state.2) answer).2.length = state.2.2.length + 1
          rw [hshape answer]
          simp
        · have hone : Pr[fun answer : HashOutput =>
              endKeep input ((CacheView.cacheOf state.1).cacheQuery input answer) |
            ($ᵗ HashOutput : ProbComp HashOutput)] ≤ ((1 : Nat) : ℝ≥0∞) * rate := by
            rw [Nat.cast_one, one_mul]
            refine hentry (CacheView.cacheOf state.1) input input ?_
            rw [← hnoticeCache]
            exact hexcludes input (CacheView.onQuery state.1 input) hnoticeFresh hright
          rw [hpot]
          refine le_trans (add_le_add (le_trans (hsplit default)
            (add_le_add hold hone)) le_rfl) ?_
          rw [add_assoc]
          exact rate_le3 rate (by omega)
      · refine ⟨(state.2.2.filter (fun entry =>
          decide (¬ becomes (CacheView.cacheOf state.1) input entry.1))).length + 1,
          gauge state + 1, fun answer _ => ?_, fun answer => ?_, ?_⟩
        · rw [potential_stepOf leftKeep rightKeep spent becomes hsettles state input answer
            hfresh, hshape answer, List.filter_append]
          simp [hself]
        · show (appendedOf leftKeep rightKeep input
            (CacheView.onQuery state.1 input, state.2) answer).2.length = state.2.2.length + 1
          rw [hshape answer]
          simp
        · have hzero : Pr[fun answer : HashOutput =>
              endKeep input ((CacheView.cacheOf state.1).cacheQuery input answer) |
            ($ᵗ HashOutput : ProbComp HashOutput)] = 0 :=
            probEvent_eq_zero fun answer _ hleftSelf => hself
              ((hsettles (CacheView.cacheOf state.1) input input answer hfresh).mp
                (hleftSpent ((CacheView.cacheOf state.1).cacheQuery input answer) input
                  hleftSelf))
          rw [hpot]
          refine le_trans (add_le_add (le_trans (hsplit default)
            (add_le_add hold (le_of_eq hzero))) le_rfl) ?_
          rw [add_zero]
          exact rate_le rate (by omega)
    · refine ⟨(state.2.2.filter (fun entry =>
        decide (¬ becomes (CacheView.cacheOf state.1) input entry.1))).length, gauge state,
        fun answer _ => ?_, fun answer => ?_, ?_⟩
      · rw [potential_stepOf leftKeep rightKeep spent becomes hsettles state input answer hfresh,
          appendedOf_of_neither leftKeep rightKeep input
            (CacheView.onQuery state.1 input, state.2) answer hleft hright]
      · show (appendedOf leftKeep rightKeep input
          (CacheView.onQuery state.1 input, state.2) answer).2.length = state.2.2.length
        rw [appendedOf_of_neither leftKeep rightKeep input
          (CacheView.onQuery state.1 input, state.2) answer hleft hright]
      · rw [hpot]
        refine le_trans (add_le_add (le_trans (probEvent_mono fun answer _ hfired => ?_) hold)
          le_rfl) (rate_le rate (by omega))
        obtain ⟨entry, hentryMem, hleftEntry⟩ := hfired
        rw [cacheOf_stepOf] at hleftEntry
        refine ⟨entry, ?_, hleftEntry⟩
        rwa [right_stepOf, appendedOf_of_neither leftKeep rightKeep input
          (CacheView.onQuery state.1 input, state.2) answer hleft hright] at hentryMem

end SlhDsaSecurity.ViewRate
