import SlhDsaSecurity.Proof.HandlerCharge

/-!
# The top of the stack, at any handler that satisfies the facts

`HandlerCharge` charges a run of the handler at the **real** availability. The game's own run is
of the handler at **total** availability, which answers every canonical input. This file closes
that gap with the handler abstract, and so finishes the parameterised copy of the stalled stack.

The argument is `ChargedProbe`'s: flag the queries where the two handlers can differ — those at
the canonical input of a node the signatures leave a child of unavailable — and the flag's law
is the same under both, because off those queries the two take the same step. That last clause
is `HandlerFacts.Lenient`, the one fact about a *pair* of handlers; everything else here is
`Facts` at each of the two availabilities.

So the three hypotheses of the top theorem are the two `Facts` and the one `Lenient`, and
`HandlerFacts` discharges all three for `lazyProgram` and for `servingProgram` alike. What comes
out is the same bound `RedrawCell.prob_game_sensitive_le` states, with the handler a parameter:
the seed-guessing avenue left standing beside it, since a query's address names its node before
any cell is read and so the record pays for each probe once.
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.HandlerLenient

open CanonicalGraph SensitiveQuery OpenCache ChargedProbe HandlerFacts

/-! ## The flagged comparison -/

open scoped Classical in
/-- The handler, with a flag set at a query where the two availabilities can differ. -/
noncomputable def sensitiveFlagged (publicSeed : Digest)
    (availableAt : Cells × Padding → HandlerCarrier.State → Node → Prop)
    (impl : Cells × Padding → QueryImpl OracleWorld (StateT HandlerState ProbComp))
    (table : Cells × Padding) :
    QueryImpl OracleWorld (StateT (HandlerState × Bool) ProbComp) :=
  fun queried state => do
    let step ← ((impl table) queried).run state.1
    pure (step.1, (step.2, state.2 ||
      decide (SensitiveQueryAt publicSeed (availableAt table) table.1 state.1 queried)))

open scoped Classical in
theorem sensitiveFlagged_run (publicSeed : Digest)
    (availableAt : Cells × Padding → HandlerCarrier.State → Node → Prop)
    (impl : Cells × Padding → QueryImpl OracleWorld (StateT HandlerState ProbComp))
    (table : Cells × Padding) (queried : OracleWorld.Domain) (state : HandlerState × Bool) :
    ((sensitiveFlagged publicSeed availableAt impl table) queried).run state =
      ((impl table) queried).run state.1 >>= fun step =>
        (pure (step.1, (step.2, state.2 ||
          decide (SensitiveQueryAt publicSeed (availableAt table) table.1 state.1 queried))) :
          ProbComp _) := rfl

open scoped Classical in
theorem sensitiveFlagged_neverFails (publicSeed : Digest)
    (availableAt flagAt : Cells × Padding → HandlerCarrier.State → Node → Prop)
    (impl : Cells × Padding → QueryImpl OracleWorld (StateT HandlerState ProbComp))
    {allowed : CanonicalGraph.Node → Prop}
    (hfacts : TableFacts publicSeed availableAt allowed impl) (table : Cells × Padding)
    (queried : OracleWorld.Domain) (state : HandlerState × Bool) :
    Pr[⊥ | ((sensitiveFlagged publicSeed flagAt impl table) queried).run state] = 0 := by
  rw [sensitiveFlagged_run, probFailure_bind_eq_add_tsum,
    hfacts.neverFails table queried state.1]
  simp

open scoped Classical in
theorem sensitiveFlagged_sticky (publicSeed : Digest)
    (flagAt : Cells × Padding → HandlerCarrier.State → Node → Prop)
    (impl : Cells × Padding → QueryImpl OracleWorld (StateT HandlerState ProbComp))
    (table : Cells × Padding) (queried : OracleWorld.Domain) (inner : HandlerState)
    (step : OracleWorld.Range queried × (HandlerState × Bool))
    (hstep : step ∈ support (((sensitiveFlagged publicSeed flagAt impl table)
      queried).run (inner, true))) : step.2.2 = true := by
  classical
  rw [sensitiveFlagged_run, mem_support_bind_iff] at hstep
  obtain ⟨value, -, hpure⟩ := hstep
  rw [support_pure, Set.mem_singleton_iff] at hpure
  rw [hpure]
  simp

open scoped Classical in
theorem sensitiveFlagged_fires (publicSeed : Digest)
    (flagAt : Cells × Padding → HandlerCarrier.State → Node → Prop)
    (impl : Cells × Padding → QueryImpl OracleWorld (StateT HandlerState ProbComp))
    (table : Cells × Padding) (queried : OracleWorld.Domain) (inner : HandlerState) (flag : Bool)
    (hbad : SensitiveQueryAt publicSeed (flagAt table) table.1 inner queried)
    (step : OracleWorld.Range queried × (HandlerState × Bool))
    (hstep : step ∈ support (((sensitiveFlagged publicSeed flagAt impl table)
      queried).run (inner, flag))) : step.2.2 = true := by
  classical
  rw [sensitiveFlagged_run, mem_support_bind_iff] at hstep
  obtain ⟨value, -, hpure⟩ := hstep
  rw [support_pure, Set.mem_singleton_iff] at hpure
  rw [hpure]
  simp [hbad]

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The lenient presentation and the strict one flag a sensitive query equally often.** -/
theorem probEvent_sensitiveFlagged_eq {α : Type} (publicSeed : Digest)
    (availableAt : Cells × Padding → HandlerCarrier.State → Node → Prop)
    (lenientImpl strictImpl :
      Cells × Padding → QueryImpl OracleWorld (StateT HandlerState ProbComp))
    {lenientAvail : Cells × Padding → HandlerCarrier.State → Node → Prop}
    {lenientAllowed : CanonicalGraph.Node → Prop}
    (hlenientFacts : TableFacts publicSeed lenientAvail lenientAllowed lenientImpl)
    {allowed : CanonicalGraph.Node → Prop}
    (hstrictFacts : TableFacts publicSeed availableAt allowed strictImpl)
    (hlenient : Lenient publicSeed availableAt lenientImpl strictImpl)
    (table : Cells × Padding) (computation : OracleComp OracleWorld α)
    (state : HandlerState × Bool) :
    Pr[fun z : α × (HandlerState × Bool) => z.2.2 = true |
      (simulateQ (sensitiveFlagged publicSeed availableAt lenientImpl table)
        computation).run state] =
      Pr[fun z : α × (HandlerState × Bool) => z.2.2 = true |
        (simulateQ (sensitiveFlagged publicSeed availableAt strictImpl table)
          computation).run state] := by
  classical
  refine LazyBridge.probEvent_flag_two_handlers_eq _ _
    (fun inner queried => SensitiveQueryAt publicSeed (availableAt table) table.1 inner queried)
    (fun queried p => sensitiveFlagged_neverFails publicSeed _ availableAt lenientImpl
      hlenientFacts table queried p)
    (fun queried p => sensitiveFlagged_neverFails publicSeed availableAt availableAt strictImpl
      hstrictFacts table queried p)
    (fun queried inner z hz => sensitiveFlagged_sticky publicSeed availableAt lenientImpl table
      queried inner z hz)
    (fun queried inner z hz => sensitiveFlagged_sticky publicSeed availableAt strictImpl table
      queried inner z hz)
    (fun queried inner flag hbad z hz => sensitiveFlagged_fires publicSeed availableAt
      lenientImpl table queried inner flag hbad z hz)
    (fun queried inner flag hbad z hz => sensitiveFlagged_fires publicSeed availableAt
      strictImpl table queried inner flag hbad z hz)
    (fun queried p hnot => ?_) computation state
  rw [sensitiveFlagged_run, sensitiveFlagged_run, hlenient.agree table queried p.1 hnot]

/-! ## The flag is the record's own event -/

open scoped Classical in
/-- **The comparison's flag says a recorded query was sensitive.** -/
theorem sensitiveFlagged_flag_iff_record {α : Type} (publicSeed : Digest)
    (availableAt flagAt : Cells × Padding → HandlerCarrier.State → Node → Prop)
    (impl : Cells × Padding → QueryImpl OracleWorld (StateT HandlerState ProbComp))
    {allowed : CanonicalGraph.Node → Prop}
    (hfacts : TableFacts publicSeed availableAt allowed impl) (table : Cells × Padding)
    (computation : OracleComp OracleWorld α) (state : HandlerState × Bool)
    (hstate : state.2 = true ↔ ∃ entry ∈ state.1.2.1,
      SensitiveEntry publicSeed (flagAt table) table.1 entry)
    (result : α × (HandlerState × Bool))
    (hresult : result ∈ support ((simulateQ
      (sensitiveFlagged publicSeed flagAt impl table) computation).run state)) :
    result.2.2 = true ↔ ∃ entry ∈ result.2.1.2.1,
      SensitiveEntry publicSeed (flagAt table) table.1 entry := by
  classical
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
    rw [hresult]
    exact hstate
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hresult
    obtain ⟨step, hstep, hrest⟩ := hresult
    refine ih step.1 step.2 ?_ result hrest
    rw [sensitiveFlagged_run, mem_support_bind_iff] at hstep
    obtain ⟨inner, hinner, hpure⟩ := hstep
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rcases queried with coin | probe
    · have hsame : inner.2.2.1 = state.1.2.1 :=
        HandlerStall.record_inl publicSeed availableAt impl hfacts table coin state.1 inner
          hinner
      have hnone : ¬ SensitiveQueryAt publicSeed (flagAt table) table.1 state.1
          (Sum.inl coin) := by
        rintro ⟨candidate, hcandidate, -⟩
        simp [probeOf] at hcandidate
      rw [hpure]
      show (state.2 || decide (SensitiveQueryAt publicSeed (flagAt table) table.1 state.1
          (Sum.inl coin))) = true ↔
        ∃ entry ∈ inner.2.2.1, SensitiveEntry publicSeed (flagAt table) table.1 entry
      rw [decide_eq_false hnone, Bool.or_false, hsame]
      exact hstate
    · have hrec : inner.2.2.1 = state.1.2.1 ++ [(probe, state.1.1)] :=
        HandlerStall.record_inr publicSeed availableAt impl hfacts table probe state.1 inner
          hinner
      have hhere : SensitiveQueryAt publicSeed (flagAt table) table.1 state.1 (Sum.inr probe) ↔
          SensitiveEntry publicSeed (flagAt table) table.1 (probe, state.1.1) := by
        constructor
        · rintro ⟨candidate, hcandidate, hsensitive⟩
          have hsame : candidate = probe := by
            have hcopy := hcandidate
            simp [probeOf] at hcopy
            exact hcopy.symm
          rw [hsame] at hsensitive
          exact hsensitive
        · intro hsensitive
          exact ⟨probe, rfl, hsensitive⟩
      rw [hpure]
      show (state.2 || decide (SensitiveQueryAt publicSeed (flagAt table) table.1 state.1
          (Sum.inr probe))) = true ↔
        ∃ entry ∈ inner.2.2.1, SensitiveEntry publicSeed (flagAt table) table.1 entry
      rw [hrec, Bool.or_eq_true, decide_eq_true_eq, hhere, hstate]
      simp [or_comm]

open scoped Classical in
/-- **The two wrappers agree off the flag.** The comparison's flag reads the cells, so the
handler carrying it is not blind to the table and the charge is not proved about it; the two
differ only in what they write to the flag. -/
theorem probEvent_sensitiveFlagged_eq_withFlag {α : Type} (publicSeed : Digest)
    (flagAt : Cells × Padding → HandlerCarrier.State → Node → Prop)
    (impl : Cells × Padding → QueryImpl OracleWorld (StateT HandlerState ProbComp))
    (table : Cells × Padding) (computation : OracleComp OracleWorld α)
    (event : α × HandlerState → Prop) :
    ∀ (inner : HandlerState) (left right : Bool),
      Pr[fun z : α × (HandlerState × Bool) => event (z.1, z.2.1) |
        (simulateQ (sensitiveFlagged publicSeed flagAt impl table)
          computation).run (inner, left)] =
        Pr[fun z : α × (HandlerState × Bool) => event (z.1, z.2.1) |
          (simulateQ (withFlag (impl table)) computation).run (inner, right)] := by
  classical
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro inner left right
    rw [simulateQ_pure, StateT.run_pure, simulateQ_pure, StateT.run_pure,
      probEvent_pure, probEvent_pure]
  | query_bind queried next ih =>
    intro inner left right
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      sensitiveFlagged_run, withFlag_run, bind_assoc, bind_assoc]
    simp only [pure_bind]
    rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
    exact tsum_congr fun step => congrArg _ (ih step.1 step.2 _ _)

open scoped Classical in
/-- **The comparison's flag is the charge's event.** At a state whose record is empty, the
lenient presentation flags exactly as often as the blind wrapper records a sensitive query. -/
theorem probEvent_flag_eq_record {α : Type} (publicSeed : Digest)
    (availableAt : Cells × Padding → HandlerCarrier.State → Node → Prop)
    (lenientImpl strictImpl :
      Cells × Padding → QueryImpl OracleWorld (StateT HandlerState ProbComp))
    {lenientAvail : Cells × Padding → HandlerCarrier.State → Node → Prop}
    {lenientAllowed : CanonicalGraph.Node → Prop}
    (hlenientFacts : TableFacts publicSeed lenientAvail lenientAllowed lenientImpl)
    {allowed : CanonicalGraph.Node → Prop}
    (hstrictFacts : TableFacts publicSeed availableAt allowed strictImpl)
    (hlenient : Lenient publicSeed availableAt lenientImpl strictImpl)
    (table : Cells × Padding) (computation : OracleComp OracleWorld α)
    (inner : HandlerState) (hinner : inner.2.1 = []) :
    Pr[fun z : α × (HandlerState × Bool) => z.2.2 = true |
      (simulateQ (sensitiveFlagged publicSeed availableAt lenientImpl table)
        computation).run (inner, false)] =
      Pr[fun z : α × (HandlerState × Bool) => ∃ entry ∈ z.2.1.2.1,
          SensitiveEntry publicSeed (availableAt table) table.1 entry |
        (simulateQ (withFlag (strictImpl table)) computation).run (inner, false)] := by
  classical
  rw [probEvent_sensitiveFlagged_eq publicSeed availableAt lenientImpl strictImpl hlenientFacts
      hstrictFacts hlenient table computation (inner, false),
    ← probEvent_sensitiveFlagged_eq_withFlag publicSeed availableAt strictImpl table computation
      (fun z : α × HandlerState => ∃ entry ∈ z.2.2.1,
        SensitiveEntry publicSeed (availableAt table) table.1 entry) inner false false]
  refine probEvent_congr' (fun z hz => ?_) rfl
  exact sensitiveFlagged_flag_iff_record publicSeed availableAt availableAt strictImpl
    hstrictFacts table computation (inner, false) (by simp [hinner]) z hz

/-! ## The charge at the game's own presentation -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
open scoped Classical in
/-- **The game's presentation makes a sensitive query off the seed at most `limit / 2 ^ 128` of
the time.** What is left standing is the seed-guessing avenue alone, charged on its own at the
same rate: a query's address names its node before any cell is read, so a probe falls in one
avenue or the other and the record pays for it once.

**The cap is taken at the end, which a half sharing its budget may not do.**
`prob_game_sensitive_le_canonical` below is this with the charge left at its expectation, and
that is the one the input half reads. -/
theorem prob_game_sensitive_le {α : Type} (publicSeed : Digest)
    (revealed : Cells × Padding → WotsKey → Fin chains → Nat)
    (signedAt : HandlerCarrier.State → ForsKey → Finset (Fin (forsTrees * 2 ^ forsHeight)))
    (lenientImpl strictImpl :
      Cells × Padding → QueryImpl OracleWorld (StateT HandlerState ProbComp))
    {lenientAvail : Cells × Padding → HandlerCarrier.State → CanonicalGraph.Node → Prop}
    {lenientAllowed : CanonicalGraph.Node → Prop}
    (hlenientFacts : TableFacts publicSeed lenientAvail lenientAllowed lenientImpl)
    {allowed : CanonicalGraph.Node → Prop}
    (hstrictFacts : TableFacts publicSeed
      (fun table cache node =>
        CanonicalGraph.Available (revealed table) (signedAt cache) node) allowed strictImpl)
    (hlenient : Lenient publicSeed
      (fun table cache node => CanonicalGraph.Available (revealed table) (signedAt cache) node)
      lenientImpl strictImpl)
    (hmono : ∀ (table : Cells × Padding) (left right : HandlerCarrier.State),
      HandlerCarrier.Grows left right →
        ∀ node, CanonicalGraph.Available (revealed table) (signedAt left) node →
          CanonicalGraph.Available (revealed table) (signedAt right) node)
    (stall : (t : OracleWorld.Domain) → OracleWorld.Range t)
    (computation : Cells × Padding → OracleComp OracleWorld α)
    (touched : CanonicalGraph.Node → Prop)
    (hcover : ∀ node, ¬ touched node → allowed node)
    (htouched : ∀ left right : Cells × Padding,
      (∀ node, touched node → left.1 node = right.1 node) →
        computation left = computation right)
    (revealedOf : α → WotsKey → Fin chains → Nat)
    (hrevealedOf : ∀ value key chain, revealedOf value key chain ≤ w - 1)
    (hreadsRevealed : ∀ (table : Cells × Padding) (value : α),
      value ∈ support (computation table) → revealedOf value = revealed table)
    (hopen : ∀ node, touched node → node ≠ CanonicalGraph.Node.secretSeed →
      ∀ (value : α) (cache : HandlerCarrier.State),
        CanonicalGraph.Available (revealedOf value) (signedAt cache) node)
    (inner : HandlerState) (hinner : inner.2.1 = []) (limit : Nat)
    (hlimit : ∀ z ∈ support (do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let pad ← ($ᵗ Padding : ProbComp Padding)
        (simulateQ (withFlag (strictImpl (cells, pad)))
          (computation (cells, pad))).run (inner, false)),
      z.2.1.2.1.length ≤ limit) :
    Pr[fun pair : (α × (HandlerState × Bool)) × Cells => pair.1.2.2 = true | (do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let pad ← ($ᵗ Padding : ProbComp Padding)
        let result ← (simulateQ (sensitiveFlagged publicSeed
          (fun table cache node =>
            CanonicalGraph.Available (revealed table) (signedAt cache) node)
          lenientImpl (cells, pad)) (computation (cells, pad))).run (inner, false)
        pure (result, cells))] ≤
      limit / ((2 ^ 128 : Nat) : ℝ≥0∞) +
        Pr[fun pair : (α × (HandlerState × Bool)) × Cells =>
            ∃ entry ∈ pair.1.2.1.2.1, RedrawCell.SensitiveAtSeed (GraphStakes.stakes publicSeed)
              (fun cache node =>
                ¬ CanonicalGraph.Available (revealedOf pair.1.1) (signedAt cache) node)
              pair.2 entry.2 entry.1 | (do
          let cells ← ($ᵗ Cells : ProbComp Cells)
          let pad ← ($ᵗ Padding : ProbComp Padding)
          let result ← (simulateQ (withFlag (strictImpl (cells, pad)))
            (computation (cells, pad))).run (inner, false)
          pure (result, cells))] := by
  classical
  rw [RedrawCell.probEvent_table_congr
    (fun table => (simulateQ (sensitiveFlagged publicSeed
      (fun table cache node =>
        CanonicalGraph.Available (revealed table) (signedAt cache) node)
      lenientImpl table) (computation table)).run (inner, false))
    (fun table => (simulateQ (withFlag (strictImpl table))
      (computation table)).run (inner, false))
    _ (fun pair => ∃ entry ∈ pair.1.2.1.2.1,
      SensitiveEntry publicSeed
        (fun cache node => CanonicalGraph.Available (revealedOf pair.1.1) (signedAt cache) node)
        pair.2 entry)
    (fun cells pad => Eq.trans (probEvent_flag_eq_record publicSeed _ lenientImpl strictImpl
        hlenientFacts hstrictFacts hlenient (cells, pad) (computation (cells, pad)) inner hinner)
      (probEvent_congr' (fun z hz => by
        rw [hreadsRevealed (cells, pad) z.1
          (HandlerCharge.value_mem_support _ _ _ z hz)]) rfl))]
  refine le_trans (probEvent_mono (q := fun pair : (α × (HandlerState × Bool)) × Cells =>
    (∃ entry ∈ pair.1.2.1.2.1, RedrawCell.SensitiveOffSeed (GraphStakes.stakes publicSeed)
        (fun cache node =>
          ¬ CanonicalGraph.Available (revealedOf pair.1.1) (signedAt cache) node)
        pair.2 entry.2 entry.1) ∨
      ∃ entry ∈ pair.1.2.1.2.1, RedrawCell.SensitiveAtSeed (GraphStakes.stakes publicSeed)
        (fun cache node =>
          ¬ CanonicalGraph.Available (revealedOf pair.1.1) (signedAt cache) node)
        pair.2 entry.2 entry.1) ?_) ?_
  · rintro pair - ⟨entry, hentry, hsensitive⟩
    rcases (RedrawCell.sensitive_iff_off_or_at_seed (GraphStakes.stakes publicSeed) _ pair.2
      entry.2 entry.1).mp (ChargedProbe.sensitive_of_sensitiveEntry publicSeed
        (revealedOf pair.1.1) (hrevealedOf pair.1.1) signedAt pair.2 entry hsensitive)
      with hoff | hatseed
    · exact Or.inl ⟨entry, hentry, hoff⟩
    · exact Or.inr ⟨entry, hentry, hatseed⟩
  refine le_trans (probEvent_or_le _ _ _) (add_le_add ?_ le_rfl)
  exact HandlerCharge.prob_sensitive_run_le publicSeed
    (fun table cache node => CanonicalGraph.Available (revealed table) (signedAt cache) node)
    strictImpl hstrictFacts hmono (GraphStakes.stakes publicSeed) stall computation touched
    hcover htouched
    (fun value cache node =>
      ¬ CanonicalGraph.Available (revealedOf value) (signedAt cache) node)
    (fun value node htouch hne cache hun => hun (hopen node htouch hne value cache))
    (fun table value hvalue => by rw [hreadsRevealed table value hvalue])
    (inner, false) limit hlimit

set_option maxRecDepth 1000000 in
open scoped Classical in
/-- **The same bound, left at its expectation.** The charge against the record is taken as an
expected count of the probes in a whole input class rather than capped at the record's length,
which is what a half sharing its budget must do: four almost-sure caps are four budgets, while
four expectations add pathwise. `prob_game_sensitive_le` above is the capped form.

`RedrawCell.prob_game_sensitive_le`, which this file's statements are copied from, has only the
capped form. The difference is deliberate and it is here rather than there because this is the
copy the input half reads, and `InputBullet.ClaimsCharged` is stated at an expectation. -/
theorem prob_game_sensitive_le_canonical {α : Type} (publicSeed : Digest)
    (revealed : Cells × Padding → WotsKey → Fin chains → Nat)
    (signedAt : HandlerCarrier.State → ForsKey → Finset (Fin (forsTrees * 2 ^ forsHeight)))
    (lenientImpl strictImpl :
      Cells × Padding → QueryImpl OracleWorld (StateT HandlerState ProbComp))
    {lenientAvail : Cells × Padding → HandlerCarrier.State → CanonicalGraph.Node → Prop}
    {lenientAllowed : CanonicalGraph.Node → Prop}
    (hlenientFacts : TableFacts publicSeed lenientAvail lenientAllowed lenientImpl)
    {allowed : CanonicalGraph.Node → Prop}
    (hstrictFacts : TableFacts publicSeed
      (fun table cache node =>
        CanonicalGraph.Available (revealed table) (signedAt cache) node) allowed strictImpl)
    (hlenient : Lenient publicSeed
      (fun table cache node => CanonicalGraph.Available (revealed table) (signedAt cache) node)
      lenientImpl strictImpl)
    (hmono : ∀ (table : Cells × Padding) (left right : HandlerCarrier.State),
      HandlerCarrier.Grows left right →
        ∀ node, CanonicalGraph.Available (revealed table) (signedAt left) node →
          CanonicalGraph.Available (revealed table) (signedAt right) node)
    (stall : (t : OracleWorld.Domain) → OracleWorld.Range t)
    (computation : Cells × Padding → OracleComp OracleWorld α)
    (touched : CanonicalGraph.Node → Prop)
    (hcover : ∀ node, ¬ touched node → allowed node)
    (htouched : ∀ left right : Cells × Padding,
      (∀ node, touched node → left.1 node = right.1 node) →
        computation left = computation right)
    (revealedOf : α → WotsKey → Fin chains → Nat)
    (hrevealedOf : ∀ value key chain, revealedOf value key chain ≤ w - 1)
    (hreadsRevealed : ∀ (table : Cells × Padding) (value : α),
      value ∈ support (computation table) → revealedOf value = revealed table)
    (hopen : ∀ node, touched node → node ≠ CanonicalGraph.Node.secretSeed →
      ∀ (value : α) (cache : HandlerCarrier.State),
        CanonicalGraph.Available (revealedOf value) (signedAt cache) node)
    (inner : HandlerState) (hinner : inner.2.1 = [])
    (keep : Bytes × HandlerCarrier.State → Bool)
    (hkeep : ∀ entry : Bytes × HandlerCarrier.State,
      RedrawCell.AimsSomewhere publicSeed entry.1 → keep entry = true) :
    Pr[fun pair : (α × (HandlerState × Bool)) × Cells => pair.1.2.2 = true | (do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let pad ← ($ᵗ Padding : ProbComp Padding)
        let result ← (simulateQ (sensitiveFlagged publicSeed
          (fun table cache node =>
            CanonicalGraph.Available (revealed table) (signedAt cache) node)
          lenientImpl (cells, pad)) (computation (cells, pad))).run (inner, false)
        pure (result, cells))] ≤
      (∑' z : α × (HandlerState × Bool),
          Pr[= z | (do
            let cells ← ($ᵗ Cells : ProbComp Cells)
            let pad ← ($ᵗ Padding : ProbComp Padding)
            (simulateQ (withFlag (strictImpl (cells, pad)))
              (computation (cells, pad))).run (inner, false))] *
            (((z.2.1.2.1.dedup.filter keep).length : Nat) : ℝ≥0∞)) /
          ((2 ^ 128 : Nat) : ℝ≥0∞) +
        Pr[fun pair : (α × (HandlerState × Bool)) × Cells =>
            ∃ entry ∈ pair.1.2.1.2.1, RedrawCell.SensitiveAtSeed (GraphStakes.stakes publicSeed)
              (fun cache node =>
                ¬ CanonicalGraph.Available (revealedOf pair.1.1) (signedAt cache) node)
              pair.2 entry.2 entry.1 | (do
          let cells ← ($ᵗ Cells : ProbComp Cells)
          let pad ← ($ᵗ Padding : ProbComp Padding)
          let result ← (simulateQ (withFlag (strictImpl (cells, pad)))
            (computation (cells, pad))).run (inner, false)
          pure (result, cells))] := by
  classical
  rw [RedrawCell.probEvent_table_congr
    (fun table => (simulateQ (sensitiveFlagged publicSeed
      (fun table cache node =>
        CanonicalGraph.Available (revealed table) (signedAt cache) node)
      lenientImpl table) (computation table)).run (inner, false))
    (fun table => (simulateQ (withFlag (strictImpl table))
      (computation table)).run (inner, false))
    _ (fun pair => ∃ entry ∈ pair.1.2.1.2.1,
      SensitiveEntry publicSeed
        (fun cache node => CanonicalGraph.Available (revealedOf pair.1.1) (signedAt cache) node)
        pair.2 entry)
    (fun cells pad => Eq.trans (probEvent_flag_eq_record publicSeed _ lenientImpl strictImpl
        hlenientFacts hstrictFacts hlenient (cells, pad) (computation (cells, pad)) inner hinner)
      (probEvent_congr' (fun z hz => by
        rw [hreadsRevealed (cells, pad) z.1
          (HandlerCharge.value_mem_support _ _ _ z hz)]) rfl))]
  refine le_trans (probEvent_mono (q := fun pair : (α × (HandlerState × Bool)) × Cells =>
    (∃ entry ∈ pair.1.2.1.2.1, RedrawCell.SensitiveOffSeed (GraphStakes.stakes publicSeed)
        (fun cache node =>
          ¬ CanonicalGraph.Available (revealedOf pair.1.1) (signedAt cache) node)
        pair.2 entry.2 entry.1) ∨
      ∃ entry ∈ pair.1.2.1.2.1, RedrawCell.SensitiveAtSeed (GraphStakes.stakes publicSeed)
        (fun cache node =>
          ¬ CanonicalGraph.Available (revealedOf pair.1.1) (signedAt cache) node)
        pair.2 entry.2 entry.1) ?_) ?_
  · rintro pair - ⟨entry, hentry, hsensitive⟩
    rcases (RedrawCell.sensitive_iff_off_or_at_seed (GraphStakes.stakes publicSeed) _ pair.2
      entry.2 entry.1).mp (ChargedProbe.sensitive_of_sensitiveEntry publicSeed
        (revealedOf pair.1.1) (hrevealedOf pair.1.1) signedAt pair.2 entry hsensitive)
      with hoff | hatseed
    · exact Or.inl ⟨entry, hentry, hoff⟩
    · exact Or.inr ⟨entry, hentry, hatseed⟩
  refine le_trans (probEvent_or_le _ _ _) (add_le_add ?_ le_rfl)
  exact HandlerCharge.prob_sensitive_run_le_canonical publicSeed
    (fun table cache node => CanonicalGraph.Available (revealed table) (signedAt cache) node)
    strictImpl hstrictFacts hmono stall computation touched hcover htouched
    (fun value cache node =>
      ¬ CanonicalGraph.Available (revealedOf value) (signedAt cache) node)
    (fun value node htouch hne cache hun => hun (hopen node htouch hne value cache))
    (fun table value hvalue => by rw [hreadsRevealed table value hvalue])
    (inner, false) keep hkeep

open scoped Classical in
/-- **The charge at the honest reveal count.** The digit a signature discloses never exceeds
`w - 1`, so that hypothesis is discharged and the handover is to the facts, monotonicity, the
record's limit, and the empty starting record.

Capped, so not the form a half sharing its budget may use:
`prob_game_sensitive_honest_le_canonical` is that one. -/
theorem prob_game_sensitive_honest_le [HasQuery HashSpec Id] {α : Type}
    (publicSeed : Digest)
    (signedAt : HandlerCarrier.State → ForsKey → Finset (Fin (forsTrees * 2 ^ forsHeight)))
    (lenientImpl strictImpl :
      Cells × Padding → QueryImpl OracleWorld (StateT HandlerState ProbComp))
    {lenientAvail : Cells × Padding → HandlerCarrier.State → CanonicalGraph.Node → Prop}
    {lenientAllowed : CanonicalGraph.Node → Prop}
    (hlenientFacts : TableFacts publicSeed lenientAvail lenientAllowed lenientImpl)
    {allowed : CanonicalGraph.Node → Prop}
    (hstrictFacts : TableFacts publicSeed
      (fun table cache node => CanonicalGraph.Available
        (GraphStakes.honestRevealed (table.1 CanonicalGraph.Node.secretSeed) publicSeed)
        (signedAt cache) node) allowed strictImpl)
    (hlenient : Lenient publicSeed
      (fun table cache node => CanonicalGraph.Available
        (GraphStakes.honestRevealed (table.1 CanonicalGraph.Node.secretSeed) publicSeed)
        (signedAt cache) node) lenientImpl strictImpl)
    (hmono : ∀ (table : Cells × Padding) (left right : HandlerCarrier.State),
      HandlerCarrier.Grows left right →
        ∀ node, CanonicalGraph.Available
            (GraphStakes.honestRevealed (table.1 CanonicalGraph.Node.secretSeed) publicSeed)
            (signedAt left) node →
          CanonicalGraph.Available
            (GraphStakes.honestRevealed (table.1 CanonicalGraph.Node.secretSeed) publicSeed)
            (signedAt right) node)
    (stall : (t : OracleWorld.Domain) → OracleWorld.Range t)
    (computation : Cells × Padding → OracleComp OracleWorld α)
    (touched : CanonicalGraph.Node → Prop)
    (hcover : ∀ node, ¬ touched node → allowed node)
    (htouched : ∀ left right : Cells × Padding,
      (∀ node, touched node → left.1 node = right.1 node) →
        computation left = computation right)
    (revealedOf : α → WotsKey → Fin chains → Nat)
    (hrevealedOf : ∀ value key chain, revealedOf value key chain ≤ w - 1)
    (hreadsRevealed : ∀ (table : Cells × Padding) (value : α),
      value ∈ support (computation table) → revealedOf value =
        GraphStakes.honestRevealed (table.1 CanonicalGraph.Node.secretSeed) publicSeed)
    (hopen : ∀ node, touched node → node ≠ CanonicalGraph.Node.secretSeed →
      ∀ (value : α) (cache : HandlerCarrier.State),
        CanonicalGraph.Available (revealedOf value) (signedAt cache) node)
    (inner : HandlerState) (hinner : inner.2.1 = []) (limit : Nat)
    (hlimit : ∀ z ∈ support (do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let pad ← ($ᵗ Padding : ProbComp Padding)
        (simulateQ (withFlag (strictImpl (cells, pad)))
          (computation (cells, pad))).run (inner, false)),
      z.2.1.2.1.length ≤ limit) :
    Pr[fun pair : (α × (HandlerState × Bool)) × Cells => pair.1.2.2 = true | (do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let pad ← ($ᵗ Padding : ProbComp Padding)
        let result ← (simulateQ (sensitiveFlagged publicSeed
          (fun table cache node => CanonicalGraph.Available
            (GraphStakes.honestRevealed (table.1 CanonicalGraph.Node.secretSeed) publicSeed)
            (signedAt cache) node)
          lenientImpl (cells, pad)) (computation (cells, pad))).run (inner, false)
        pure (result, cells))] ≤
      limit / ((2 ^ 128 : Nat) : ℝ≥0∞) +
        Pr[fun pair : (α × (HandlerState × Bool)) × Cells =>
            ∃ entry ∈ pair.1.2.1.2.1, RedrawCell.SensitiveAtSeed (GraphStakes.stakes publicSeed)
              (fun cache node =>
                ¬ CanonicalGraph.Available (revealedOf pair.1.1) (signedAt cache) node)
              pair.2 entry.2 entry.1 | (do
          let cells ← ($ᵗ Cells : ProbComp Cells)
          let pad ← ($ᵗ Padding : ProbComp Padding)
          let result ← (simulateQ (withFlag (strictImpl (cells, pad)))
            (computation (cells, pad))).run (inner, false)
          pure (result, cells))] :=
  prob_game_sensitive_le publicSeed
    (fun table => GraphStakes.honestRevealed (table.1 CanonicalGraph.Node.secretSeed) publicSeed)
    signedAt lenientImpl strictImpl
    hlenientFacts hstrictFacts hlenient hmono stall computation touched hcover htouched
    revealedOf hrevealedOf hreadsRevealed hopen inner hinner limit hlimit

open scoped Classical in
/-- **The charge at the honest reveal count, left at its expectation.** The digit a signature
discloses never exceeds `w - 1`, so that hypothesis is discharged and the handover is to the
facts, monotonicity, the class the count is taken over, and the empty starting record. This is
the shape `InputBullet.ClaimsCharged` is stated at. -/
theorem prob_game_sensitive_honest_le_canonical [HasQuery HashSpec Id] {α : Type}
    (publicSeed : Digest)
    (signedAt : HandlerCarrier.State → ForsKey → Finset (Fin (forsTrees * 2 ^ forsHeight)))
    (lenientImpl strictImpl :
      Cells × Padding → QueryImpl OracleWorld (StateT HandlerState ProbComp))
    {lenientAvail : Cells × Padding → HandlerCarrier.State → CanonicalGraph.Node → Prop}
    {lenientAllowed : CanonicalGraph.Node → Prop}
    (hlenientFacts : TableFacts publicSeed lenientAvail lenientAllowed lenientImpl)
    {allowed : CanonicalGraph.Node → Prop}
    (hstrictFacts : TableFacts publicSeed
      (fun table cache node => CanonicalGraph.Available
        (GraphStakes.honestRevealed (table.1 CanonicalGraph.Node.secretSeed) publicSeed)
        (signedAt cache) node) allowed strictImpl)
    (hlenient : Lenient publicSeed
      (fun table cache node => CanonicalGraph.Available
        (GraphStakes.honestRevealed (table.1 CanonicalGraph.Node.secretSeed) publicSeed)
        (signedAt cache) node) lenientImpl strictImpl)
    (hmono : ∀ (table : Cells × Padding) (left right : HandlerCarrier.State),
      HandlerCarrier.Grows left right →
        ∀ node, CanonicalGraph.Available
            (GraphStakes.honestRevealed (table.1 CanonicalGraph.Node.secretSeed) publicSeed)
            (signedAt left) node →
          CanonicalGraph.Available
            (GraphStakes.honestRevealed (table.1 CanonicalGraph.Node.secretSeed) publicSeed)
            (signedAt right) node)
    (stall : (t : OracleWorld.Domain) → OracleWorld.Range t)
    (computation : Cells × Padding → OracleComp OracleWorld α)
    (touched : CanonicalGraph.Node → Prop)
    (hcover : ∀ node, ¬ touched node → allowed node)
    (htouched : ∀ left right : Cells × Padding,
      (∀ node, touched node → left.1 node = right.1 node) →
        computation left = computation right)
    (revealedOf : α → WotsKey → Fin chains → Nat)
    (hrevealedOf : ∀ value key chain, revealedOf value key chain ≤ w - 1)
    (hreadsRevealed : ∀ (table : Cells × Padding) (value : α),
      value ∈ support (computation table) → revealedOf value =
        GraphStakes.honestRevealed (table.1 CanonicalGraph.Node.secretSeed) publicSeed)
    (hopen : ∀ node, touched node → node ≠ CanonicalGraph.Node.secretSeed →
      ∀ (value : α) (cache : HandlerCarrier.State),
        CanonicalGraph.Available (revealedOf value) (signedAt cache) node)
    (inner : HandlerState) (hinner : inner.2.1 = [])
    (keep : Bytes × HandlerCarrier.State → Bool)
    (hkeep : ∀ entry : Bytes × HandlerCarrier.State,
      RedrawCell.AimsSomewhere publicSeed entry.1 → keep entry = true) :
    Pr[fun pair : (α × (HandlerState × Bool)) × Cells => pair.1.2.2 = true | (do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let pad ← ($ᵗ Padding : ProbComp Padding)
        let result ← (simulateQ (sensitiveFlagged publicSeed
          (fun table cache node => CanonicalGraph.Available
            (GraphStakes.honestRevealed (table.1 CanonicalGraph.Node.secretSeed) publicSeed)
            (signedAt cache) node)
          lenientImpl (cells, pad)) (computation (cells, pad))).run (inner, false)
        pure (result, cells))] ≤
      (∑' z : α × (HandlerState × Bool),
          Pr[= z | (do
            let cells ← ($ᵗ Cells : ProbComp Cells)
            let pad ← ($ᵗ Padding : ProbComp Padding)
            (simulateQ (withFlag (strictImpl (cells, pad)))
              (computation (cells, pad))).run (inner, false))] *
            (((z.2.1.2.1.dedup.filter keep).length : Nat) : ℝ≥0∞)) /
          ((2 ^ 128 : Nat) : ℝ≥0∞) +
        Pr[fun pair : (α × (HandlerState × Bool)) × Cells =>
            ∃ entry ∈ pair.1.2.1.2.1, RedrawCell.SensitiveAtSeed (GraphStakes.stakes publicSeed)
              (fun cache node =>
                ¬ CanonicalGraph.Available (revealedOf pair.1.1) (signedAt cache) node)
              pair.2 entry.2 entry.1 | (do
          let cells ← ($ᵗ Cells : ProbComp Cells)
          let pad ← ($ᵗ Padding : ProbComp Padding)
          let result ← (simulateQ (withFlag (strictImpl (cells, pad)))
            (computation (cells, pad))).run (inner, false)
          pure (result, cells))] :=
  prob_game_sensitive_le_canonical publicSeed
    (fun table => GraphStakes.honestRevealed (table.1 CanonicalGraph.Node.secretSeed) publicSeed)
    signedAt lenientImpl strictImpl hlenientFacts hstrictFacts hlenient hmono stall computation
    touched hcover htouched revealedOf hrevealedOf hreadsRevealed hopen inner hinner keep
    hkeep

end SlhDsaSecurity.HandlerLenient
