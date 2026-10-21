import SlhDsaSecurity.Proof.OpenCache
import SlhDsaSecurity.Proof.StalledRun

/-!
# Which cell a probe is charged against, and the flag that records it

`OpenCache.evalDist_stalled_lazyProgram_congr` says the stalled run does not mention the cell
it stalled on. To use it the charge has to be expressed as an event about that run, and a
probe has to be charged against *one* cell rather than against the table as a whole. This file
does both.

**One cell per probe.** `SensitiveAt` names the cell a candidate is charged against, and
`sensitiveAt_unique` is the lemma that keeps the rate at one unit per probe:
`Stakes.locate` reads the node off the address before any cell is consulted, and `Stakes.stake`
reads the cell off the node, so a candidate is charged against at most one cell. The events
"this probe is charged against cell `i`" are therefore disjoint as `i` ranges over the cells,
and summing them counts each probe once. Stated loosely — a bound per cell, added over cells —
the same sum would come to `|Index| / 2 ^ 128` per probe, which is useless; that is why the
disjointness is a named lemma and not a step inside a calculation.

**The flag.** `StalledRun.probEvent_flag_stalled_eq` wants the event carried as a sticky flag in
the handler's state, so `flagged` is `OpenCache.lazyProgram` with one added: a flag set when a
probe is charged against the stalled cell. It reads that cell, which is exactly why it is a
different handler from the blind one and why the two are only ever joined through the record —
`flag_iff_record` is that joining, and it is the only place their relationship is used.

The three hypotheses the stalled comparison takes hold for concrete reasons: the handler never
fails, availability only grows along a run so a released cell stays released, and a charge
requires the cell to be unavailable, so none can arise once it is released.
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 40000

namespace SlhDsaSecurity.ChargedProbe

open CanonicalGraph SensitiveQuery OpenCache

variable {Node : Type}

/-! ## One cell per probe -/

/-- A candidate input is charged **against a given cell**: it is the canonical input of a node
staking that cell, and the signatures have not made it available. -/
def SensitiveAt (stakes : Stakes Node CanonicalGraph.Node)
    (unavailable : QueryCache HashSpec → CanonicalGraph.Node → Prop) (cells : Cells)
    (cache : QueryCache HashSpec) (candidate : Bytes) (index : CanonicalGraph.Node) : Prop :=
  ∃ node : Node, stakes.stake node = index ∧ unavailable cache index ∧
    stakes.inputOf node (cells index) = candidate

/-- Being charged at some cell is being charged. -/
theorem sensitive_iff_exists (stakes : Stakes Node CanonicalGraph.Node)
    (unavailable : QueryCache HashSpec → CanonicalGraph.Node → Prop) (cells : Cells)
    (cache : QueryCache HashSpec) (candidate : Bytes) :
    Sensitive stakes unavailable cells cache candidate ↔
      ∃ index, SensitiveAt stakes unavailable cells cache candidate index := by
  constructor
  · rintro ⟨node, hunavailable, hinput⟩
    exact ⟨stakes.stake node, node, rfl, hunavailable, hinput⟩
  · rintro ⟨index, node, hstake, hunavailable, hinput⟩
    exact ⟨node, hstake ▸ hunavailable, hstake ▸ hinput⟩

/-- **A probe is charged against at most one cell.** The address names the node before any cell
is read and the node names the cell, so the events "this probe is charged against cell `i`" are
disjoint as `i` ranges over the cells — which is what makes their sum one unit per probe rather
than one per cell. -/
theorem sensitiveAt_unique (stakes : Stakes Node CanonicalGraph.Node)
    (unavailable : QueryCache HashSpec → CanonicalGraph.Node → Prop) (cells : Cells)
    (cache : QueryCache HashSpec) (candidate : Bytes) {first second : CanonicalGraph.Node}
    (hfirst : SensitiveAt stakes unavailable cells cache candidate first)
    (hsecond : SensitiveAt stakes unavailable cells cache candidate second) :
    first = second := by
  obtain ⟨node, hstake, -, hinput⟩ := hfirst
  obtain ⟨other, hother, -, hotherInput⟩ := hsecond
  have hnodes : node = other := by
    have hleft : stakes.locate candidate = some node := by
      rw [← hinput, stakes.locate_inputOf]
    have hright : stakes.locate candidate = some other := by
      rw [← hotherInput, stakes.locate_inputOf]
    exact Option.some.inj (hleft.symm.trans hright)
  rw [← hstake, ← hother, hnodes]


/-! ## The cell a probe targets, and why the counts add

The charge against one cell is weighted by how many probes aim at that cell. What makes the
weighting legitimate is that aiming is decided by the probe's bytes alone: `Stakes.locate`
reads the node off the address and `Stakes.stake` reads the cell off the node, so no cell is
consulted and the count is a function of the record. And what makes the weights add to the
number of probes rather than to `|Index|` times it is that a probe aims at one cell —
`targets_unique`, the same uniqueness as `sensitiveAt_unique` with the table dropped. Summing
the per-cell charges *unweighted* would give `|Index| / 2 ^ 128` per probe and be useless; the
weights are the whole point. -/

/-- The cell a probe aims at, read off its address alone. No cell is consulted, so this is a
property of the probe and the state, not of the table. -/
def Targets (stakes : Stakes Node CanonicalGraph.Node)
    (unavailable : QueryCache HashSpec → CanonicalGraph.Node → Prop)
    (index : CanonicalGraph.Node) (entry : Bytes × QueryCache HashSpec) : Prop :=
  ∃ node : Node, stakes.stake node = index ∧ unavailable entry.2 index ∧
    stakes.locate entry.1 = some node

/-- A charged probe aims where it is charged. -/
theorem targets_of_sensitiveAt (stakes : Stakes Node CanonicalGraph.Node)
    (unavailable : QueryCache HashSpec → CanonicalGraph.Node → Prop) (cells : Cells)
    (index : CanonicalGraph.Node) (entry : Bytes × QueryCache HashSpec)
    (hcharged : SensitiveAt stakes unavailable cells entry.2 entry.1 index) :
    Targets stakes unavailable index entry := by
  obtain ⟨node, hstake, hunavailable, hinput⟩ := hcharged
  exact ⟨node, hstake, hunavailable, by rw [← hinput, stakes.locate_inputOf]⟩

/-- **A probe aims at one cell.** -/
theorem targets_unique (stakes : Stakes Node CanonicalGraph.Node)
    (unavailable : QueryCache HashSpec → CanonicalGraph.Node → Prop)
    (entry : Bytes × QueryCache HashSpec) {first second : CanonicalGraph.Node}
    (hfirst : Targets stakes unavailable first entry)
    (hsecond : Targets stakes unavailable second entry) : first = second := by
  obtain ⟨node, hstake, -, hlocate⟩ := hfirst
  obtain ⟨other, hother, -, hotherLocate⟩ := hsecond
  rw [← hstake, ← hother, Option.some.inj (hlocate.symm.trans hotherLocate)]

set_option linter.constructorNameAsVariable false in
open scoped Classical in
/-- **The weights add to the number of probes.** -/
theorem sum_targets_length_le (stakes : Stakes Node CanonicalGraph.Node)
    (unavailable : QueryCache HashSpec → CanonicalGraph.Node → Prop)
    (probes : List (Bytes × QueryCache HashSpec)) :
    ∑ index : CanonicalGraph.Node,
        (probes.filter (fun entry => decide (Targets stakes unavailable index entry))).length ≤
      probes.length := by
  classical
  induction probes with
  | nil => simp
  | cons entry rest ih =>
    have hone : ∑ index : CanonicalGraph.Node,
        (if Targets stakes unavailable index entry then 1 else 0) ≤ 1 := by
      rw [← Finset.card_filter]
      refine Finset.card_le_one.mpr fun first hfirst second hsecond => ?_
      rw [Finset.mem_filter] at hfirst hsecond
      exact targets_unique stakes unavailable entry hfirst.2 hsecond.2
    have hsplit : ∀ index : CanonicalGraph.Node,
        ((entry :: rest).filter
            (fun other => decide (Targets stakes unavailable index other))).length =
          (if Targets stakes unavailable index entry then 1 else 0) +
            (rest.filter (fun other => decide (Targets stakes unavailable index other))).length := by
      intro index
      by_cases hentry : Targets stakes unavailable index entry
      · rw [List.filter_cons_of_pos (by simpa using hentry), List.length_cons, if_pos hentry]
        omega
      · rw [List.filter_cons_of_neg (by simpa using hentry), if_neg hentry]
        omega
    simp only [hsplit, Finset.sum_add_distrib, List.length_cons]
    omega

/-! ## The per-cell charge at a fixed record

Against a record fixed in advance, the cells are drawn afterwards and only the probes aiming at
a given cell can be charged against it, each with the probability that one coordinate takes one
value. -/

open scoped Classical in
/-- **The charge against one cell, weighted by the probes aiming at it.** -/
theorem prob_list_sensitiveAt_le (stakes : Stakes Node CanonicalGraph.Node)
    (unavailable : QueryCache HashSpec → CanonicalGraph.Node → Prop)
    (index : CanonicalGraph.Node) (probes : List (Bytes × QueryCache HashSpec)) :
    Pr[fun cells : Cells =>
        ∃ entry ∈ probes, SensitiveAt stakes unavailable cells entry.2 entry.1 index |
      ($ᵗ Cells : ProbComp Cells)] ≤
      (probes.filter (fun entry => decide (Targets stakes unavailable index entry))).length /
        ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  refine le_trans (probEvent_mono (q := fun cells : Cells =>
    ∃ entry ∈ (probes.filter
        (fun other => decide (Targets stakes unavailable index other))).toFinset,
      SensitiveAt stakes unavailable cells entry.2 entry.1 index) ?_) ?_
  · rintro cells - ⟨entry, hentry, hcharged⟩
    refine ⟨entry, List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hentry, ?_⟩), hcharged⟩
    simpa using targets_of_sensitiveAt stakes unavailable cells index entry hcharged
  refine le_trans (probEvent_exists_finset_le_sum _ _ _) ?_
  calc ∑ entry ∈ (probes.filter
        (fun other => decide (Targets stakes unavailable index other))).toFinset,
        Pr[fun cells : Cells =>
            SensitiveAt stakes unavailable cells entry.2 entry.1 index |
          ($ᵗ Cells : ProbComp Cells)]
      ≤ ∑ _entry ∈ (probes.filter
          (fun other => decide (Targets stakes unavailable index other))).toFinset,
          1 / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
        refine Finset.sum_le_sum fun entry _ => ?_
        refine le_trans (probEvent_mono (q := fun cells : Cells =>
          Sensitive stakes unavailable cells entry.2 entry.1) ?_) ?_
        · intro cells _ hcharged
          exact (sensitive_iff_exists stakes unavailable cells entry.2 entry.1).mpr
            ⟨index, hcharged⟩
        · exact prob_sensitive_le stakes unavailable entry.2 entry.1
    _ = (probes.filter
          (fun other => decide (Targets stakes unavailable index other))).toFinset.card *
          (1 / ((2 ^ 128 : Nat) : ℝ≥0∞)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((probes.filter
          (fun other => decide (Targets stakes unavailable index other))).length : ℝ≥0∞) *
          (1 / ((2 ^ 128 : Nat) : ℝ≥0∞)) := by
        refine mul_le_mul' (Nat.cast_le.mpr ?_) le_rfl
        exact (probes.filter
          (fun other => decide (Targets stakes unavailable index other))).toFinset_card_le
    _ = _ := by rw [mul_one_div]

open scoped Classical in
/-- **The charge at a fixed record, summed over the cells.** Each probe is counted once,
because it aims at one cell. -/
theorem prob_list_sensitive_le_of_sum (stakes : Stakes Node CanonicalGraph.Node)
    (unavailable : QueryCache HashSpec → CanonicalGraph.Node → Prop)
    (probes : List (Bytes × QueryCache HashSpec)) :
    ∑ index : CanonicalGraph.Node,
        Pr[fun cells : Cells =>
            ∃ entry ∈ probes, SensitiveAt stakes unavailable cells entry.2 entry.1 index |
          ($ᵗ Cells : ProbComp Cells)] ≤
      probes.length / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  calc ∑ index : CanonicalGraph.Node,
        Pr[fun cells : Cells =>
            ∃ entry ∈ probes, SensitiveAt stakes unavailable cells entry.2 entry.1 index |
          ($ᵗ Cells : ProbComp Cells)]
      ≤ ∑ index : CanonicalGraph.Node,
          ((probes.filter
            (fun entry => decide (Targets stakes unavailable index entry))).length : ℝ≥0∞) /
              ((2 ^ 128 : Nat) : ℝ≥0∞) :=
        Finset.sum_le_sum fun index _ =>
          prob_list_sensitiveAt_le stakes unavailable index probes
    _ = (∑ index : CanonicalGraph.Node,
          ((probes.filter
            (fun entry => decide (Targets stakes unavailable index entry))).length : ℝ≥0∞)) /
              ((2 ^ 128 : Nat) : ℝ≥0∞) := by
        simp only [div_eq_mul_inv, ← Finset.sum_mul]
    _ ≤ (probes.length : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
        refine ENNReal.div_le_div_right ?_ _
        rw [← Nat.cast_sum]
        exact Nat.cast_le.mpr (sum_targets_length_le stakes unavailable probes)


/-! ## The charge against one cell, with that cell alone drawn

Being charged against a given cell reads the table at that one coordinate and nowhere else, so
the charge can be stated against a single uniform cell rather than a whole uniform table. That
is what lets it be applied to a run which is blind to that coordinate but not to the others:
the coordinate may be drawn after the run, and the weight is then the expected number of probes
aiming at it. -/

/-- A probe charged against a cell, as a condition on that cell alone. -/
def ChargedBy (stakes : Stakes Node CanonicalGraph.Node)
    (unavailable : QueryCache HashSpec → CanonicalGraph.Node → Prop)
    (index : CanonicalGraph.Node) (cell : Cell) (entry : Bytes × QueryCache HashSpec) : Prop :=
  ∃ node : Node, stakes.stake node = index ∧ unavailable entry.2 index ∧
    stakes.inputOf node cell = entry.1

/-- It is being charged, with the cell read off the table. -/
theorem chargedBy_iff (stakes : Stakes Node CanonicalGraph.Node)
    (unavailable : QueryCache HashSpec → CanonicalGraph.Node → Prop) (cells : Cells)
    (index : CanonicalGraph.Node) (entry : Bytes × QueryCache HashSpec) :
    ChargedBy stakes unavailable index (cells index) entry ↔
      SensitiveAt stakes unavailable cells entry.2 entry.1 index := Iff.rfl

/-- A probe charged by a cell aims at it. -/
theorem targets_of_chargedBy (stakes : Stakes Node CanonicalGraph.Node)
    (unavailable : QueryCache HashSpec → CanonicalGraph.Node → Prop)
    (index : CanonicalGraph.Node) (cell : Cell) (entry : Bytes × QueryCache HashSpec)
    (hcharged : ChargedBy stakes unavailable index cell entry) :
    Targets stakes unavailable index entry := by
  obtain ⟨node, hstake, hunavailable, hinput⟩ := hcharged
  exact ⟨node, hstake, hunavailable, by rw [← hinput, stakes.locate_inputOf]⟩

open scoped Classical in
/-- **One probe, one cell.** At most one value of the cell charges a given probe, so a uniform
cell charges it with the probability of a single guess. -/
theorem prob_cell_entry_le (stakes : Stakes Node CanonicalGraph.Node)
    (unavailable : QueryCache HashSpec → CanonicalGraph.Node → Prop)
    (index : CanonicalGraph.Node) (entry : Bytes × QueryCache HashSpec) :
    Pr[fun cell : Cell => ChargedBy stakes unavailable index cell entry |
      ($ᵗ Cell : ProbComp Cell)] ≤ 1 / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  by_cases hwitness : ∃ cell : Cell, ChargedBy stakes unavailable index cell entry
  · obtain ⟨value, node, hstake, hunavailable, hinput⟩ := hwitness
    refine le_of_le_of_eq (probEvent_mono (q := fun cell : Cell => value = cell) ?_) ?_
    · rintro cell - ⟨other, -, -, hotherInput⟩
      have hsame : other = node := by
        have hleft : stakes.locate entry.1 = some other := by
          rw [← hotherInput, stakes.locate_inputOf]
        have hright : stakes.locate entry.1 = some node := by
          rw [← hinput, stakes.locate_inputOf]
        exact Option.some.inj (hleft.symm.trans hright)
      subst hsame
      exact stakes.inputOf_injective other (hinput.trans hotherInput.symm)
    · exact SecretGuessCharge.prob_single_guess value
  · refine le_of_eq_of_le (b := 0) (probEvent_eq_zero fun cell _ hbad => ?_) (by simp)
    exact hwitness ⟨cell, hbad⟩

open scoped Classical in
/-- **The charge against one cell at a fixed record**, with that cell alone drawn. -/
theorem prob_cell_list_le (stakes : Stakes Node CanonicalGraph.Node)
    (unavailable : QueryCache HashSpec → CanonicalGraph.Node → Prop)
    (index : CanonicalGraph.Node) (probes : List (Bytes × QueryCache HashSpec)) :
    Pr[fun cell : Cell => ∃ entry ∈ probes, ChargedBy stakes unavailable index cell entry |
      ($ᵗ Cell : ProbComp Cell)] ≤
      (probes.filter (fun entry => decide (Targets stakes unavailable index entry))).length /
        ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  refine le_trans (probEvent_mono (q := fun cell : Cell =>
    ∃ entry ∈ (probes.filter
        (fun other => decide (Targets stakes unavailable index other))).toFinset,
      ChargedBy stakes unavailable index cell entry) ?_) ?_
  · rintro cell - ⟨entry, hentry, hcharged⟩
    refine ⟨entry, List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hentry, ?_⟩), hcharged⟩
    simpa using targets_of_chargedBy stakes unavailable index cell entry hcharged
  refine le_trans (probEvent_exists_finset_le_sum _ _ _) ?_
  calc ∑ entry ∈ (probes.filter
        (fun other => decide (Targets stakes unavailable index other))).toFinset,
        Pr[fun cell : Cell => ChargedBy stakes unavailable index cell entry |
          ($ᵗ Cell : ProbComp Cell)]
      ≤ ∑ _entry ∈ (probes.filter
          (fun other => decide (Targets stakes unavailable index other))).toFinset,
          1 / ((2 ^ 128 : Nat) : ℝ≥0∞) :=
        Finset.sum_le_sum fun entry _ => prob_cell_entry_le stakes unavailable index entry
    _ = (probes.filter
          (fun other => decide (Targets stakes unavailable index other))).toFinset.card *
          (1 / ((2 ^ 128 : Nat) : ℝ≥0∞)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((probes.filter
          (fun other => decide (Targets stakes unavailable index other))).length : ℝ≥0∞) *
          (1 / ((2 ^ 128 : Nat) : ℝ≥0∞)) := by
        refine mul_le_mul' (Nat.cast_le.mpr ?_) le_rfl
        exact (probes.filter
          (fun other => decide (Targets stakes unavailable index other))).toFinset_card_le
    _ = _ := by rw [mul_one_div]

/-! ## The weight becomes an expectation

With the cell drawn after the run, the fixed-record bound averages: the charge against one cell
is the expected number of probes aiming at it, over `2 ^ 128`. Nothing about the run is assumed
except that it does not draw the cell. -/

open scoped Classical in
/-- The number of probes a record aims at a given cell. -/
noncomputable def aiming (stakes : Stakes Node CanonicalGraph.Node)
    (unavailable : QueryCache HashSpec → CanonicalGraph.Node → Prop)
    (index : CanonicalGraph.Node) (probes : List (Bytes × QueryCache HashSpec)) : Nat :=
  (probes.filter (fun entry => decide (Targets stakes unavailable index entry))).length

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The charge against one cell, over a run that does not draw it.** -/
theorem prob_run_cell_le {γ : Type} (stakes : Stakes Node CanonicalGraph.Node)
    (unavailable : QueryCache HashSpec → CanonicalGraph.Node → Prop)
    (index : CanonicalGraph.Node) (run : ProbComp γ)
    (record : γ → List (Bytes × QueryCache HashSpec)) :
    Pr[fun pair : γ × Cell =>
        ∃ entry ∈ record pair.1, ChargedBy stakes unavailable index pair.2 entry |
      (do
        let result ← run
        let cell ← ($ᵗ Cell : ProbComp Cell)
        pure (result, cell))] ≤
      (∑' result, Pr[= result | run] *
        ((aiming stakes unavailable index (record result) : Nat) : ℝ≥0∞)) /
          ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  rw [probEvent_bind_eq_tsum]
  calc ∑' result, Pr[= result | run] *
        Pr[fun pair : γ × Cell =>
            ∃ entry ∈ record pair.1, ChargedBy stakes unavailable index pair.2 entry |
          (do
            let cell ← ($ᵗ Cell : ProbComp Cell)
            pure (result, cell))]
      ≤ ∑' result, Pr[= result | run] *
          (((aiming stakes unavailable index (record result) : Nat) : ℝ≥0∞) /
            ((2 ^ 128 : Nat) : ℝ≥0∞)) := by
        refine ENNReal.tsum_le_tsum fun result => ?_
        by_cases hmem : result ∈ support run
        · refine mul_le_mul' le_rfl ?_
          rw [bind_pure_comp, probEvent_map]
          exact prob_cell_list_le stakes unavailable index (record result)
        · rw [probOutput_eq_zero_of_not_mem_support hmem, zero_mul]
          simp
    _ = _ := by
        simp only [div_eq_mul_inv, ← mul_assoc]
        rw [ENNReal.tsum_mul_right]


/-- **A finite sum and an expectation may be exchanged.** Over `ℝ≥0∞` both sides are defined and
equal whatever the summands; it is stated for an arbitrary index set because this is the step at
which a factor of the index count would hide, and a general statement is easier to check than
one specialised to a type with `2 ^ 26` elements. -/
theorem sum_tsum_comm {Index Result : Type} [DecidableEq Index] (nodes : Finset Index)
    (summand : Index → Result → ℝ≥0∞) :
    ∑ index ∈ nodes, ∑' result : Result, summand index result =
      ∑' result : Result, ∑ index ∈ nodes, summand index result := by
  refine Finset.induction_on nodes ?_ ?_
  · simp
  · intro head rest hhead ih
    rw [Finset.sum_insert hhead, ih, ← ENNReal.tsum_add]
    exact tsum_congr fun result => by rw [Finset.sum_insert hhead]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
open scoped Classical in
/-- **The charge over all the cells.** Each cell's charge is weighted by the probes aiming at
it, and those weights add to the number of probes, so the whole run costs one unit per probe
rather than one per cell per probe. The exchange of the sum over cells with the expectation
over runs is carried out through `tsum_fintype` and `ENNReal.tsum_comm` rather than left to the
index type being finite, since it is the step at which a factor of the number of cells would
hide. -/
theorem prob_run_sensitive_le {γ : Type} (stakes : Stakes Node CanonicalGraph.Node)
    (unavailable : QueryCache HashSpec → CanonicalGraph.Node → Prop) (run : ProbComp γ)
    (record : γ → List (Bytes × QueryCache HashSpec)) (limit : Nat)
    (hlimit : ∀ result ∈ support run, (record result).length ≤ limit) :
    ∑ index : CanonicalGraph.Node,
        Pr[fun pair : γ × Cell =>
            ∃ entry ∈ record pair.1, ChargedBy stakes unavailable index pair.2 entry |
          (do
            let result ← run
            let cell ← ($ᵗ Cell : ProbComp Cell)
            pure (result, cell))] ≤
      limit / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  refine le_trans (Finset.sum_le_sum fun index _ =>
    prob_run_cell_le stakes unavailable index run record) ?_
  calc ∑ index : CanonicalGraph.Node,
        (∑' result, Pr[= result | run] *
          ((aiming stakes unavailable index (record result) : Nat) : ℝ≥0∞)) /
            ((2 ^ 128 : Nat) : ℝ≥0∞)
      = (∑ index : CanonicalGraph.Node, ∑' result, Pr[= result | run] *
          ((aiming stakes unavailable index (record result) : Nat) : ℝ≥0∞)) /
            ((2 ^ 128 : Nat) : ℝ≥0∞) := by
        simp only [div_eq_mul_inv, ← Finset.sum_mul]
    _ = (∑' result, ∑ index : CanonicalGraph.Node, Pr[= result | run] *
          ((aiming stakes unavailable index (record result) : Nat) : ℝ≥0∞)) /
            ((2 ^ 128 : Nat) : ℝ≥0∞) := by
        refine congrArg (fun total => total / ((2 ^ 128 : Nat) : ℝ≥0∞)) ?_
        exact sum_tsum_comm Finset.univ fun index result =>
          Pr[= result | run] *
            ((aiming stakes unavailable index (record result) : Nat) : ℝ≥0∞)
    _ ≤ (∑' result, Pr[= result | run] * (limit : ℝ≥0∞)) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
        refine ENNReal.div_le_div_right (ENNReal.tsum_le_tsum fun result => ?_) _
        rw [← Finset.mul_sum]
        by_cases hmem : result ∈ support run
        · refine mul_le_mul' le_rfl ?_
          rw [← Nat.cast_sum]
          refine Nat.cast_le.mpr (le_trans ?_ (hlimit result hmem))
          exact sum_targets_length_le stakes unavailable (record result)
        · rw [probOutput_eq_zero_of_not_mem_support hmem, zero_mul, zero_mul]
    _ ≤ (1 * (limit : ℝ≥0∞)) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
        refine ENNReal.div_le_div_right ?_ _
        rw [ENNReal.tsum_mul_right]
        exact mul_le_mul' tsum_probOutput_le_one le_rfl
    _ = _ := by rw [one_mul]

/-! ## The flag -/

/-- The probe a query makes, if it makes one. -/
def probeOf : OracleWorld.Domain → Option Bytes
  | Sum.inl _ => none
  | Sum.inr input => some input

/-- A recorded entry charged against a given cell. -/
def Charged (stakes : Stakes Node CanonicalGraph.Node)
    (unavailable : QueryCache HashSpec → CanonicalGraph.Node → Prop) (cells : Cells)
    (index : CanonicalGraph.Node) (entry : Bytes × QueryCache HashSpec) : Prop :=
  SensitiveAt stakes unavailable cells entry.2 entry.1 index

/-- A query charged against a given cell at a given state. -/
def ChargedHere (stakes : Stakes Node CanonicalGraph.Node)
    (unavailable : QueryCache HashSpec → CanonicalGraph.Node → Prop) (cells : Cells)
    (index : CanonicalGraph.Node) (state : HandlerState)
    (queried : OracleWorld.Domain) : Prop :=
  ∃ input, probeOf queried = some input ∧
    SensitiveAt stakes unavailable cells state.1 input index

variable (publicSeed : Digest)

open scoped Classical in
/-- **The flagged handler**: the one that answers only what a run may legitimately compute,
with a sticky flag set when a probe is charged against `index`. -/
noncomputable def flagged (availableAt : QueryCache HashSpec → CanonicalGraph.Node → Prop)
    (stakes : Stakes Node CanonicalGraph.Node) (index : CanonicalGraph.Node)
    (table : Cells × Padding) :
    QueryImpl OracleWorld (StateT (HandlerState × Bool) ProbComp) :=
  fun queried state => do
    let step ← ((lazyProgram publicSeed availableAt table) queried).run state.1
    pure (step.1, (step.2, state.2 ||
      decide (ChargedHere stakes (fun cache index => ¬ availableAt cache index) table.1 index
        state.1 queried)))

open scoped Classical in
theorem flagged_run (availableAt : QueryCache HashSpec → CanonicalGraph.Node → Prop)
    (stakes : Stakes Node CanonicalGraph.Node) (index : CanonicalGraph.Node)
    (table : Cells × Padding) (queried : OracleWorld.Domain) (state : HandlerState × Bool) :
    ((flagged publicSeed availableAt stakes index table) queried).run state =
      ((lazyProgram publicSeed availableAt table) queried).run state.1 >>= fun step =>
        (pure (step.1, (step.2, state.2 ||
          decide (ChargedHere stakes (fun cache index => ¬ availableAt cache index) table.1
            index state.1 queried))) : ProbComp _) := rfl


open scoped Classical in
/-- A private sample leaves the handler's state alone. -/
theorem lazyProgram_step_inl (availableAt : QueryCache HashSpec → CanonicalGraph.Node → Prop)
    (table : Cells × Padding) (coin : unifSpec.Domain) (state : HandlerState)
    (step : OracleWorld.Range (Sum.inl coin) × HandlerState)
    (hstep : step ∈ support (((lazyProgram publicSeed availableAt table)
      (Sum.inl coin)).run state)) : step.2 = state := by
  rw [lazyProgram_run_inl, mem_support_bind_iff] at hstep
  obtain ⟨value, -, hpure⟩ := hstep
  rw [support_pure, Set.mem_singleton_iff] at hpure
  exact congrArg Prod.snd hpure

open scoped Classical in
/-- A hash query records itself with the cache it was issued against. -/
theorem lazyProgram_step_inr (availableAt : QueryCache HashSpec → CanonicalGraph.Node → Prop)
    (table : Cells × Padding) (input : Bytes) (state : HandlerState)
    (step : OracleWorld.Range (Sum.inr input) × HandlerState)
    (hstep : step ∈ support (((lazyProgram publicSeed availableAt table)
      (Sum.inr input)).run state)) : step.2.2.1 = state.2.1 ++ [(input, state.1)] := by
  rw [lazyProgram_run_inr, mem_support_bind_iff] at hstep
  obtain ⟨inner, -, hpure⟩ := hstep
  rw [support_pure, Set.mem_singleton_iff] at hpure
  rw [hpure]

/-! ## What the stalled comparison takes

Three facts, each for a concrete reason: the handler never fails, availability only grows along
a run so a released cell stays released, and a charge requires the cell to be unavailable, so
none can arise once it is released. -/

open scoped Classical in
/-- The handler never fails. -/
theorem lazyProgram_neverFails (availableAt : QueryCache HashSpec → CanonicalGraph.Node → Prop)
    (table : Cells × Padding) (queried : OracleWorld.Domain) (state : HandlerState) :
    Pr[⊥ | ((lazyProgram publicSeed availableAt table) queried).run state] = 0 := by
  classical
  rcases queried with coin | input
  · rw [lazyProgram_run_inl]
    simp
  · rw [lazyProgram_run_inr]
    cases hcached : state.1 input with
    | some cached => simp
    | none =>
      cases hopen : openCache publicSeed (availableAt state.1) table input with
      | some answer => simp
      | none => simp

open scoped Classical in
/-- Cache entries survive a step, so what a run has determined only grows. -/
theorem lazyProgram_cache_mono (availableAt : QueryCache HashSpec → CanonicalGraph.Node → Prop)
    (table : Cells × Padding) (queried : OracleWorld.Domain) (state : HandlerState)
    (step : OracleWorld.Range queried × HandlerState)
    (hstep : step ∈ support (((lazyProgram publicSeed availableAt table) queried).run state))
    (probe : Bytes) (hprobe : state.1 probe ≠ none) : step.2.1 probe ≠ none := by
  classical
  rcases queried with coin | input
  · rw [lazyProgram_run_inl, mem_support_bind_iff] at hstep
    obtain ⟨value, -, hpure⟩ := hstep
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [hpure]
    exact hprobe
  · rw [lazyProgram_run_inr, mem_support_bind_iff] at hstep
    obtain ⟨inner, hinner, hpure⟩ := hstep
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [hpure]
    show inner.2 probe ≠ none
    have hgrow : inner.2 = state.1 ∨
        ∃ answer : HashOutput, inner.2 = state.1.cacheQuery input answer := by
      revert hinner
      cases hcached : state.1 input with
      | some cached =>
        intro hinner
        simp only [support_pure, Set.mem_singleton_iff] at hinner
        exact Or.inl (congrArg Prod.snd hinner)
      | none =>
        cases hopen : openCache publicSeed (availableAt state.1) table input with
        | some answer =>
          intro hinner
          simp only [support_pure, Set.mem_singleton_iff] at hinner
          exact Or.inr ⟨answer, congrArg Prod.snd hinner⟩
        | none =>
          intro hinner
          simp only [support_map] at hinner
          obtain ⟨sampled, -, hpair⟩ := hinner
          exact Or.inr ⟨sampled, (congrArg Prod.snd hpair).symm⟩
    rcases hgrow with hsame | ⟨answer, hcache⟩
    · rw [hsame]; exact hprobe
    · rw [hcache]
      by_cases hsame : probe = input
      · subst hsame
        rw [QueryCache.cacheQuery_self]
        simp
      · rw [QueryCache.cacheQuery_of_ne state.1 answer hsame]
        exact hprobe

open scoped Classical in
/-- The flagged handler never fails either. -/
theorem flagged_neverFails (availableAt : QueryCache HashSpec → CanonicalGraph.Node → Prop)
    (stakes : Stakes Node CanonicalGraph.Node) (index : CanonicalGraph.Node)
    (table : Cells × Padding) (queried : OracleWorld.Domain) (state : HandlerState × Bool) :
    Pr[⊥ | ((flagged publicSeed availableAt stakes index table) queried).run state] = 0 := by
  rw [flagged_run, probFailure_bind_eq_add_tsum,
    lazyProgram_neverFails publicSeed availableAt table queried state.1]
  simp

open scoped Classical in
/-- **A released cell stays released.** Availability grows with the cache, and the cache only
grows, so a state where the cell is available is followed by states where it is. -/
theorem flagged_frozen (availableAt : QueryCache HashSpec → CanonicalGraph.Node → Prop)
    (hmono : ∀ (left right : QueryCache HashSpec),
      (∀ probe, left probe ≠ none → right probe ≠ none) →
        ∀ node, availableAt left node → availableAt right node)
    (stakes : Stakes Node CanonicalGraph.Node) (index : CanonicalGraph.Node)
    (table : Cells × Padding) (queried : OracleWorld.Domain) (state : HandlerState × Bool)
    (hstate : availableAt state.1.1 index)
    (step : OracleWorld.Range queried × (HandlerState × Bool))
    (hstep : step ∈ support (((flagged publicSeed availableAt stakes index table) queried).run
      state)) : availableAt step.2.1.1 index := by
  classical
  rw [flagged_run, mem_support_bind_iff] at hstep
  obtain ⟨inner, hinner, hpure⟩ := hstep
  rw [support_pure, Set.mem_singleton_iff] at hpure
  rw [hpure]
  exact hmono state.1.1 inner.2.1
    (fun probe hprobe =>
      lazyProgram_cache_mono publicSeed availableAt table queried state.1 inner hinner probe
        hprobe)
    index hstate

open scoped Classical in
/-- **No charge arises once the cell is released.** A charge needs the cell to be unavailable,
so a state where it is available is followed by states with the same flag. -/
theorem flagged_quiet (availableAt : QueryCache HashSpec → CanonicalGraph.Node → Prop)
    (stakes : Stakes Node CanonicalGraph.Node) (index : CanonicalGraph.Node)
    (table : Cells × Padding) (queried : OracleWorld.Domain) (state : HandlerState × Bool)
    (hstate : availableAt state.1.1 index)
    (step : OracleWorld.Range queried × (HandlerState × Bool))
    (hstep : step ∈ support (((flagged publicSeed availableAt stakes index table) queried).run
      state)) : step.2.2 = state.2 := by
  classical
  rw [flagged_run, mem_support_bind_iff] at hstep
  obtain ⟨inner, -, hpure⟩ := hstep
  rw [support_pure, Set.mem_singleton_iff] at hpure
  rw [hpure]
  show (state.2 || decide (ChargedHere stakes (fun cache node => ¬ availableAt cache node)
    table.1 index state.1 queried)) = state.2
  have hnone : ¬ ChargedHere stakes (fun cache node => ¬ availableAt cache node) table.1 index
      state.1 queried := by
    rintro ⟨probe, -, -, -, hunavailable, -⟩
    exact hunavailable hstate
  rw [decide_eq_false hnone, Bool.or_false]

/-! ## The flag is the record

The only place the flagged handler and the blind one are related: they record the same probes,
and the flag says exactly that one of them was charged. -/

open scoped Classical in
/-- **The flag says that a recorded probe was charged.** -/
theorem flag_iff_record {α : Type}
    (availableAt : QueryCache HashSpec → CanonicalGraph.Node → Prop)
    (stakes : Stakes Node CanonicalGraph.Node) (index : CanonicalGraph.Node)
    (table : Cells × Padding) (computation : OracleComp OracleWorld α)
    (state : HandlerState × Bool)
    (hstate : state.2 = true ↔ ∃ entry ∈ state.1.2.1,
      Charged stakes (fun cache node => ¬ availableAt cache node) table.1 index entry)
    (result : α × (HandlerState × Bool))
    (hresult : result ∈ support ((simulateQ
      (flagged publicSeed availableAt stakes index table) computation).run state)) :
    result.2.2 = true ↔ ∃ entry ∈ result.2.1.2.1,
      Charged stakes (fun cache node => ¬ availableAt cache node) table.1 index entry := by
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
    rw [flagged_run, mem_support_bind_iff] at hstep
    obtain ⟨inner, hinner, hpure⟩ := hstep
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rcases queried with coin | probe
    · have hsame : inner.2 = state.1 :=
        lazyProgram_step_inl publicSeed availableAt table coin state.1 inner hinner
      have hnone : ¬ ChargedHere stakes (fun cache node => ¬ availableAt cache node) table.1
          index state.1 (Sum.inl coin) := by
        rintro ⟨candidate, hcandidate, -⟩
        simp [probeOf] at hcandidate
      rw [hpure]
      show (state.2 || decide (ChargedHere stakes
          (fun cache node => ¬ availableAt cache node) table.1 index state.1 (Sum.inl coin)))
            = true ↔
        ∃ entry ∈ inner.2.2.1,
          Charged stakes (fun cache node => ¬ availableAt cache node) table.1 index entry
      rw [decide_eq_false hnone, Bool.or_false, hsame]
      exact hstate
    · have hrec : inner.2.2.1 = state.1.2.1 ++ [(probe, state.1.1)] :=
        lazyProgram_step_inr publicSeed availableAt table probe state.1 inner hinner
      have hhere : ChargedHere stakes (fun cache node => ¬ availableAt cache node) table.1 index
          state.1 (Sum.inr probe) ↔
          Charged stakes (fun cache node => ¬ availableAt cache node) table.1 index
            (probe, state.1.1) := by
        constructor
        · rintro ⟨candidate, hcandidate, hsensitive⟩
          have hsame : candidate = probe := by
            have := hcandidate
            simp [probeOf] at this
            exact this.symm
          rw [hsame] at hsensitive
          exact hsensitive
        · intro hcharged
          exact ⟨probe, rfl, hcharged⟩
      rw [hpure]
      show (state.2 || decide (ChargedHere stakes
          (fun cache node => ¬ availableAt cache node) table.1 index state.1 (Sum.inr probe)))
            = true ↔
        ∃ entry ∈ inner.2.2.1,
          Charged stakes (fun cache node => ¬ availableAt cache node) table.1 index entry
      rw [hrec, Bool.or_eq_true, decide_eq_true_eq, hhere, hstate]
      simp [or_comm]


/-! ## The weight does not notice the stall

The probes a record aims at a cell are all made while that cell is unavailable, so a run
stalled at the moment it becomes available aims at it exactly as often as the unstalled one.
That is frozen-insensitivity of the count, and `StalledRun.expectation_stalled_eq` turns it
into equality of the expectations — which is what lets the per-cell weights be summed under one
measure rather than under one measure per cell. -/

open scoped Classical in
/-- Carrying a flag it does not touch leaves the handler failure-free. -/
theorem withFlag_neverFails (availableAt : QueryCache HashSpec → CanonicalGraph.Node → Prop)
    (table : Cells × Padding) (queried : OracleWorld.Domain) (state : HandlerState × Bool) :
    Pr[⊥ | ((withFlag (lazyProgram publicSeed availableAt table)) queried).run state] = 0 := by
  rw [withFlag_run, probFailure_bind_eq_add_tsum,
    lazyProgram_neverFails publicSeed availableAt table queried state.1]
  simp

open scoped Classical in
/-- A released cell stays released, the flag being untouched. -/
theorem withFlag_frozen (availableAt : QueryCache HashSpec → CanonicalGraph.Node → Prop)
    (hmono : ∀ (left right : QueryCache HashSpec),
      (∀ probe, left probe ≠ none → right probe ≠ none) →
        ∀ node, availableAt left node → availableAt right node)
    (index : CanonicalGraph.Node) (table : Cells × Padding)
    (queried : OracleWorld.Domain) (state : HandlerState × Bool)
    (hstate : availableAt state.1.1 index)
    (step : OracleWorld.Range queried × (HandlerState × Bool))
    (hstep : step ∈ support (((withFlag (lazyProgram publicSeed availableAt table))
      queried).run state)) : availableAt step.2.1.1 index := by
  classical
  rw [withFlag_run, mem_support_bind_iff] at hstep
  obtain ⟨inner, hinner, hpure⟩ := hstep
  rw [support_pure, Set.mem_singleton_iff] at hpure
  rw [hpure]
  exact hmono state.1.1 inner.2.1
    (fun probe hprobe =>
      lazyProgram_cache_mono publicSeed availableAt table queried state.1 inner hinner probe
        hprobe)
    index hstate

open scoped Classical in
/-- **Once the cell is released nothing more aims at it**, so the count stands still. -/
theorem withFlag_aiming_quiet (availableAt : QueryCache HashSpec → CanonicalGraph.Node → Prop)
    (stakes : Stakes Node CanonicalGraph.Node) (index : CanonicalGraph.Node)
    (table : Cells × Padding) (queried : OracleWorld.Domain) (state : HandlerState × Bool)
    (hstate : availableAt state.1.1 index)
    (step : OracleWorld.Range queried × (HandlerState × Bool))
    (hstep : step ∈ support (((withFlag (lazyProgram publicSeed availableAt table))
      queried).run state)) :
    aiming stakes (fun cache node => ¬ availableAt cache node) index step.2.1.2.1 =
      aiming stakes (fun cache node => ¬ availableAt cache node) index state.1.2.1 := by
  classical
  rw [withFlag_run, mem_support_bind_iff] at hstep
  obtain ⟨inner, hinner, hpure⟩ := hstep
  rw [support_pure, Set.mem_singleton_iff] at hpure
  rw [hpure]
  show aiming stakes (fun cache node => ¬ availableAt cache node) index inner.2.2.1 = _
  rcases queried with coin | probe
  · rw [lazyProgram_step_inl publicSeed availableAt table coin state.1 inner hinner]
  · rw [lazyProgram_step_inr publicSeed availableAt table probe state.1 inner hinner]
    have hnot : ¬ Targets stakes (fun cache node => ¬ availableAt cache node) index
        (probe, state.1.1) := by
      rintro ⟨-, -, hunavailable, -⟩
      exact hunavailable hstate
    have hsingle : List.filter
        (fun entry => decide (Targets stakes (fun cache node => ¬ availableAt cache node)
          index entry)) [(probe, state.1.1)] = [] := by
      rw [List.filter_cons_of_neg (by simpa using hnot), List.filter_nil]
    simp only [aiming, List.filter_append, hsingle, List.append_nil]

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The expected number of probes aiming at a cell is the same stalled and unstalled.** The
equality is between the real run and the run stalled at that same cell, and it holds because
the count cannot change once the cell is released — not because of anything about the sum over
cells. -/
theorem expected_aiming_stalled_eq {α : Type}
    (availableAt : QueryCache HashSpec → CanonicalGraph.Node → Prop)
    (hmono : ∀ (left right : QueryCache HashSpec),
      (∀ probe, left probe ≠ none → right probe ≠ none) →
        ∀ node, availableAt left node → availableAt right node)
    (stakes : Stakes Node CanonicalGraph.Node) (index : CanonicalGraph.Node)
    (table : Cells × Padding) (stall : (t : OracleWorld.Domain) → OracleWorld.Range t)
    (computation : OracleComp OracleWorld α) (state : HandlerState × Bool) :
    (∑' z : α × (HandlerState × Bool),
        Pr[= z | (simulateQ (withFlag (lazyProgram publicSeed availableAt table))
            computation).run state] *
          ((aiming stakes (fun cache node => ¬ availableAt cache node) index z.2.1.2.1 :
            Nat) : ℝ≥0∞)) =
      ∑' z : α × (HandlerState × Bool),
        Pr[= z | (simulateQ (StalledRun.stalled
            (withFlag (lazyProgram publicSeed availableAt table))
            (fun inner => availableAt inner.1 index) stall) computation).run state] *
          ((aiming stakes (fun cache node => ¬ availableAt cache node) index z.2.1.2.1 :
            Nat) : ℝ≥0∞) :=
  StalledRun.expectation_stalled_eq (withFlag (lazyProgram publicSeed availableAt table))
    (fun inner => availableAt inner.1 index) stall
    (fun p => ((aiming stakes (fun cache node => ¬ availableAt cache node) index p.1.2.1 :
      Nat) : ℝ≥0∞))
    (fun queried p => withFlag_neverFails publicSeed availableAt table queried p)
    (fun queried p hp z hz =>
      withFlag_frozen publicSeed availableAt hmono index table queried p hp z hz)
    (fun queried p hp z hz => by
      exact_mod_cast congrArg (fun count : Nat => (count : ℝ≥0∞))
        (withFlag_aiming_quiet publicSeed availableAt stakes index table queried p hp z hz))
    computation state


/-! ## The charge itself does not notice the stall

A charge needs the cell unavailable, so none can arise after the stall. "Some recorded probe is
charged against this cell" is therefore as frozen-insensitive as the count is, and
`StalledRun.expectation_stalled_eq` applies to its indicator directly. The flag the stalled
comparison was built around is not needed for it: the event is already a function of the
record, which the handler carries. -/

open scoped Classical in
/-- Once the cell is released nothing more is charged against it. -/
theorem withFlag_charged_quiet (availableAt : QueryCache HashSpec → CanonicalGraph.Node → Prop)
    (stakes : Stakes Node CanonicalGraph.Node) (index : CanonicalGraph.Node)
    (table : Cells × Padding) (queried : OracleWorld.Domain) (state : HandlerState × Bool)
    (hstate : availableAt state.1.1 index)
    (step : OracleWorld.Range queried × (HandlerState × Bool))
    (hstep : step ∈ support (((withFlag (lazyProgram publicSeed availableAt table))
      queried).run state)) :
    ((∃ entry ∈ step.2.1.2.1, ChargedBy stakes (fun cache node => ¬ availableAt cache node)
        index (table.1 index) entry) ↔
      ∃ entry ∈ state.1.2.1, ChargedBy stakes (fun cache node => ¬ availableAt cache node)
        index (table.1 index) entry) := by
  classical
  rw [withFlag_run, mem_support_bind_iff] at hstep
  obtain ⟨inner, hinner, hpure⟩ := hstep
  rw [support_pure, Set.mem_singleton_iff] at hpure
  rw [hpure]
  show (∃ entry ∈ inner.2.2.1, _) ↔ _
  rcases queried with coin | probe
  · rw [lazyProgram_step_inl publicSeed availableAt table coin state.1 inner hinner]
  · rw [lazyProgram_step_inr publicSeed availableAt table probe state.1 inner hinner]
    have hnot : ¬ ChargedBy stakes (fun cache node => ¬ availableAt cache node) index
        (table.1 index) (probe, state.1.1) := by
      rintro ⟨-, -, hunavailable, -⟩
      exact hunavailable hstate
    constructor
    · rintro ⟨entry, hentry, hcharged⟩
      rcases List.mem_append.mp hentry with hleft | hright
      · exact ⟨entry, hleft, hcharged⟩
      · rw [List.mem_singleton.mp hright] at hcharged
        exact absurd hcharged hnot
    · rintro ⟨entry, hentry, hcharged⟩
      exact ⟨entry, List.mem_append.mpr (Or.inl hentry), hcharged⟩

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **Stalling does not change the chance of a charged probe.** -/
theorem prob_charged_stalled_eq {α : Type}
    (availableAt : QueryCache HashSpec → CanonicalGraph.Node → Prop)
    (hmono : ∀ (left right : QueryCache HashSpec),
      (∀ probe, left probe ≠ none → right probe ≠ none) →
        ∀ node, availableAt left node → availableAt right node)
    (stakes : Stakes Node CanonicalGraph.Node) (index : CanonicalGraph.Node)
    (table : Cells × Padding) (stall : (t : OracleWorld.Domain) → OracleWorld.Range t)
    (computation : OracleComp OracleWorld α) (state : HandlerState × Bool) :
    Pr[fun z : α × (HandlerState × Bool) =>
        ∃ entry ∈ z.2.1.2.1, ChargedBy stakes
          (fun cache node => ¬ availableAt cache node) index (table.1 index) entry |
      (simulateQ (withFlag (lazyProgram publicSeed availableAt table))
        computation).run state] =
      Pr[fun z : α × (HandlerState × Bool) =>
          ∃ entry ∈ z.2.1.2.1, ChargedBy stakes
            (fun cache node => ¬ availableAt cache node) index (table.1 index) entry |
        (simulateQ (StalledRun.stalled (withFlag (lazyProgram publicSeed availableAt table))
          (fun inner => availableAt inner.1 index) stall) computation).run state] := by
  classical
  have hform : ∀ run : ProbComp (α × (HandlerState × Bool)),
      Pr[fun z : α × (HandlerState × Bool) =>
          ∃ entry ∈ z.2.1.2.1, ChargedBy stakes
            (fun cache node => ¬ availableAt cache node) index (table.1 index) entry | run] =
        ∑' z : α × (HandlerState × Bool), Pr[= z | run] *
          (if ∃ entry ∈ z.2.1.2.1, ChargedBy stakes
            (fun cache node => ¬ availableAt cache node) index (table.1 index) entry
            then 1 else 0) := by
    intro run
    rw [probEvent_eq_tsum_ite]
    refine tsum_congr fun z => ?_
    by_cases hz : ∃ entry ∈ z.2.1.2.1, ChargedBy stakes
        (fun cache node => ¬ availableAt cache node) index (table.1 index) entry
    · simp [hz]
    · simp [hz]
  rw [hform, hform]
  exact StalledRun.expectation_stalled_eq (withFlag (lazyProgram publicSeed availableAt table))
    (fun inner => availableAt inner.1 index) stall
    (fun p => if ∃ entry ∈ p.1.2.1, ChargedBy stakes
      (fun cache node => ¬ availableAt cache node) index (table.1 index) entry then 1 else 0)
    (fun queried p => withFlag_neverFails publicSeed availableAt table queried p)
    (fun queried p hp z hz =>
      withFlag_frozen publicSeed availableAt hmono index table queried p hp z hz)
    (fun queried p hp z hz => if_congr
      (withFlag_charged_quiet publicSeed availableAt stakes index table queried p hp z hz)
      rfl rfl) computation state

end SlhDsaSecurity.ChargedProbe
