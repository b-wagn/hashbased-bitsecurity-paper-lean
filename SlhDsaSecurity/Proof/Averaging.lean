import SlhDsaSecurity.Proof.Security

/-!
# Averaging a bound over a prefix

The warmed game draws its seeds and walks the canonical graph before the adversary runs, and
every charge then applies to the rest of the run with the cells held fixed. Turning those
per-prefix bounds into a bound on the whole run is the one probabilistic step involved, and it
is the obvious one: a bound that holds for every value of the prefix holds on average.

Stated for a prefix whose value is kept — which is what the halves need, since the event they
describe names the prefix's cells.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.Averaging

/-- **A bound that holds after every prefix holds over the pair.** -/
theorem probEvent_bind_pair_le {α β : Type} (first : ProbComp α) (rest : α → ProbComp β)
    (event : α → β → Prop) (bound : ℝ≥0∞)
    (hrest : ∀ value ∈ support first, Pr[event value | rest value] ≤ bound) :
    Pr[fun pair : α × β => event pair.1 pair.2 |
        (do let value ← first; let result ← rest value; pure (value, result))] ≤ bound := by
  rw [probEvent_bind_eq_tsum]
  calc ∑' value, Pr[= value | first] *
        Pr[fun pair : α × β => event pair.1 pair.2 |
          rest value >>= fun result => pure (value, result)]
      = ∑' value, Pr[= value | first] * Pr[event value | rest value] :=
        tsum_congr fun value => congrArg _ (by rw [bind_pure_comp, probEvent_map]; rfl)
    _ ≤ ∑' value, Pr[= value | first] * bound := by
        refine ENNReal.tsum_le_tsum fun value => ?_
        by_cases hmem : value ∈ support first
        · exact mul_le_mul' le_rfl (hrest value hmem)
        · rw [probOutput_eq_zero_of_not_mem_support hmem, zero_mul]
          exact zero_le
    _ = (∑' value, Pr[= value | first]) * bound := ENNReal.tsum_mul_right
    _ ≤ 1 * bound := mul_le_mul' tsum_probOutput_le_one le_rfl
    _ = bound := one_mul bound

end SlhDsaSecurity.Averaging
