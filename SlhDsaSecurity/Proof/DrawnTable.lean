import SlhDsaSecurity.Proof.SensitiveQuery
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling

/-!
# Drawing the cells early buys a prober nothing

`SensitiveQuery.prob_record_sensitive_le` charges a prober one unit of `2 ^ -128` per probe
with the cell table drawn *after* the run. A presentation that draws a cell when a probe first
names its node — which is what makes a lazy handler commute with its eager counterpart at every
step — seems to put the later probes at a worse rate: a second probe at a node whose cell was
drawn at an earlier, missed probe is conditioned on that miss, so it matches with probability
`1 / (2 ^ 128 - m)` rather than `1 / 2 ^ 128`.

Summing those conditional rates would give `q / (2 ^ 128 - q)`, hence an additive `q ^ 2 / 2 ^ 256`
on top of `q / 2 ^ 128`. That term is not inside any slack: nothing bounds `q` below `2 ^ 127`,
where it reaches about a quarter. So the sum of conditional rates is not a usable bound, and
the question is whether the rate is really conditional.

It is not, and the reason is that summing conditional rates double-counts. Reaching the `k`-th
probe at all requires having missed the earlier ones, and the two factors cancel:

    Pr[the k-th probe is the first hit]
      = Pr[no earlier hit] * Pr[hit now | no earlier hit]
      = ((2 ^ 128 - m) / 2 ^ 128) * (1 / (2 ^ 128 - m))
      = 1 / 2 ^ 128 .

This file makes that exact rather than asymptotic, by removing the conditioning instead of
estimating it. Until the first hit **every answer a prober receives is "miss"**, so what it
probes next is a function of its own earlier probes and of nothing else: the probes it makes
while it keeps missing form a *determined* list, `missRun`. The event "it ever hits within
`limit` probes" is contained in "the table meets that determined list", and a determined list
of length `limit` is met with probability at most `limit / 2 ^ 128` — the fully deferred
counting of `prob_list_sensitive_le`, with no conditioning anywhere.

So the rate is `limit / 2 ^ 128` exactly, with no additive term.

**Two caveats the Lean does not carry.** The "drawn during the run" reading is prose only:
nothing instantiates `strategy` from a lazily-sampling handler, and the containment asserted
above — that "it ever hits within `limit` probes" sits inside "the table meets that determined
list" — is stated nowhere in Lean. `prob_mixture_missRun_sensitive_le` is the intended patch, by
folding the answers into table-independent coins, but the folding is `TableBlind`'s lifting and
is never composed with it.

And `prob_table_first_sensitive_le` records the draw **order** only. Its run is typed
`ProbComp γ`, which cannot read the table at all, so it says nothing about "a presentation with
the table in its state" — the case where the run *does* read it. `TableBlind`'s header states
the obstruction bluntly: two caches built from tables that differ are told apart by a single
query at a canonical input where they differ, so no run-level congruence holds.
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.DrawnTable

open SensitiveQuery

variable {Node Index State : Type} [Fintype Index] [DecidableEq Index]

/-! ## A determined list of probes -/

open scoped Classical in
/-- **A fixed list of probes meets the table at one unit per probe.** No order of drawing is
involved: the list is fixed and the table is uniform. -/
theorem prob_list_sensitive_le (stakes : Stakes Node Index)
    (unavailable : State → Index → Prop) (probes : List (Bytes × State)) :
    Pr[fun table : Index → Cell =>
        ∃ entry ∈ probes, Sensitive stakes unavailable table entry.2 entry.1 |
      ($ᵗ (Index → Cell) : ProbComp (Index → Cell))] ≤
      probes.length / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  refine le_trans (probEvent_mono (q := fun table : Index → Cell =>
    ∃ entry ∈ probes.toFinset, Sensitive stakes unavailable table entry.2 entry.1) ?_) ?_
  · rintro table - ⟨entry, hentry, hsensitive⟩
    exact ⟨entry, List.mem_toFinset.mpr hentry, hsensitive⟩
  refine le_trans (probEvent_exists_finset_le_sum _ _ _) ?_
  calc ∑ entry ∈ probes.toFinset,
        Pr[fun table : Index → Cell =>
            Sensitive stakes unavailable table entry.2 entry.1 |
          ($ᵗ (Index → Cell) : ProbComp (Index → Cell))]
      ≤ ∑ _entry ∈ probes.toFinset, 1 / ((2 ^ 128 : Nat) : ℝ≥0∞) :=
        Finset.sum_le_sum fun entry _ =>
          prob_sensitive_le stakes unavailable entry.2 entry.1
    _ = probes.toFinset.card * (1 / ((2 ^ 128 : Nat) : ℝ≥0∞)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (probes.length : ℝ≥0∞) * (1 / ((2 ^ 128 : Nat) : ℝ≥0∞)) := by
        refine mul_le_mul' (Nat.cast_le.mpr probes.toFinset_card_le) le_rfl
    _ = _ := by rw [mul_one_div]

/-! ## Miss feedback buys nothing

A prober that draws the cell it names and is told whether it matched is told "miss" every time
until the first hit. So the probes it makes while it keeps missing are a function of its own
earlier probes, and nothing else: they are determined before any cell is drawn. -/

/-- The probes a prober makes while every answer is "miss". -/
def missRun (strategy : List (Bytes × State) → Bytes × State) : Nat → List (Bytes × State)
  | 0 => []
  | n + 1 => missRun strategy n ++ [strategy (missRun strategy n)]

@[simp] theorem missRun_length (strategy : List (Bytes × State) → Bytes × State) (n : Nat) :
    (missRun strategy n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [missRun, List.length_append, ih]; rfl

/-- **Feedback buys nothing.** A prober that is told whether each probe matched meets the table
with probability at most one unit per probe, exactly as one that is told nothing: until the
first match its answers carry no information, so the probes it would make are determined before
any cell is drawn. -/
theorem prob_missRun_sensitive_le (stakes : Stakes Node Index)
    (unavailable : State → Index → Prop)
    (strategy : List (Bytes × State) → Bytes × State) (limit : Nat) :
    Pr[fun table : Index → Cell =>
        ∃ entry ∈ missRun strategy limit,
          Sensitive stakes unavailable table entry.2 entry.1 |
      ($ᵗ (Index → Cell) : ProbComp (Index → Cell))] ≤
      limit / ((2 ^ 128 : Nat) : ℝ≥0∞) :=
  le_of_le_of_eq (prob_list_sensitive_le stakes unavailable (missRun strategy limit))
    (by rw [missRun_length])

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- The same for a prober with private coins, drawn independently of the cells. -/
theorem prob_mixture_missRun_sensitive_le {Aux : Type} (stakes : Stakes Node Index)
    (unavailable : State → Index → Prop) (coins : ProbComp Aux)
    (strategy : Aux → List (Bytes × State) → Bytes × State) (limit : Nat) :
    Pr[fun pair : Aux × (Index → Cell) =>
        ∃ entry ∈ missRun (strategy pair.1) limit,
          Sensitive stakes unavailable pair.2 entry.2 entry.1 |
      (do
        let aux ← coins
        let table ← ($ᵗ (Index → Cell) : ProbComp (Index → Cell))
        pure (aux, table))] ≤
      limit / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  rw [probEvent_bind_eq_tsum]
  calc ∑' aux, Pr[= aux | coins] *
        Pr[fun pair : Aux × (Index → Cell) =>
            ∃ entry ∈ missRun (strategy pair.1) limit,
              Sensitive stakes unavailable pair.2 entry.2 entry.1 |
          (do
            let table ← ($ᵗ (Index → Cell) : ProbComp (Index → Cell))
            pure (aux, table))]
      ≤ ∑' aux, Pr[= aux | coins] * (limit / ((2 ^ 128 : Nat) : ℝ≥0∞)) := by
        refine ENNReal.tsum_le_tsum fun aux => mul_le_mul' le_rfl ?_
        rw [bind_pure_comp, probEvent_map]
        exact prob_missRun_sensitive_le stakes unavailable (strategy aux) limit
    _ = (∑' aux, Pr[= aux | coins]) * (limit / ((2 ^ 128 : Nat) : ℝ≥0∞)) :=
        ENNReal.tsum_mul_right
    _ ≤ 1 * (limit / ((2 ^ 128 : Nat) : ℝ≥0∞)) :=
        mul_le_mul' tsum_probOutput_le_one le_rfl
    _ = _ := one_mul _

/-! ## The table drawn first

A presentation that carries the table in its state draws it before the run rather than after.
The two orders are the same bound, the draws being independent. -/

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The table may be drawn before the run.** -/
theorem prob_table_first_sensitive_le {γ : Type} (stakes : Stakes Node Index)
    (unavailable : State → Index → Prop) (run : ProbComp γ)
    (record : γ → List (Bytes × State))
    (limit : Nat) (hlimit : ∀ result ∈ support run, (record result).length ≤ limit) :
    Pr[fun pair : γ × (Index → Cell) =>
        ∃ entry ∈ record pair.1, Sensitive stakes unavailable pair.2 entry.2 entry.1 |
      (do
        let table ← ($ᵗ (Index → Cell) : ProbComp (Index → Cell))
        let result ← run
        pure (result, table))] ≤
      limit / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  refine le_trans (le_of_eq (probEvent_congr' (fun _ _ => Iff.rfl) ?_))
    (prob_record_sensitive_le stakes unavailable run record limit hlimit)
  exact (OracleComp.DeferredSampling.evalDist_bind_comm run
    ($ᵗ (Index → Cell) : ProbComp (Index → Cell))
    (fun result table => pure (result, table))).symm

end SlhDsaSecurity.DrawnTable
