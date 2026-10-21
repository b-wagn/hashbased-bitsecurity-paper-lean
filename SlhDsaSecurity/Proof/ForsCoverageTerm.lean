import SlhDsaSecurity.Proof.GrowthCharge
import SlhDsaSecurity.Proof.ForsCoverage
import SlhDsaSecurity.Proof.MessageDigest

/-!
# The FORS coverage term

`GrowthCharge.prob_badWithin_le` charges a run whenever each individual fresh answer is bad
for its own input with probability at most `p`. For the FORS term the bad event is "the
answer parses to a digest all of whose fourteen FORS positions are already disclosed", and
the per-call probability is exactly what `ForsCoverage` computes: a uniform thirty-byte
answer parses to a uniform `View` (`MessageDigest.evalDist_parse_uniform`), and a uniform
view is covered with probability `(∑ i ∏ t |revealed i t|) / 2 ^ 231`, which the load cap
`∑ i loads i ^ 14 ≤ 2 ^ 103` bounds by `2 ^ -128`.

So `prob_coverage_within_le` charges the whole run at `limit / 2 ^ 128` against a disclosure
set fixed in advance. The adaptivity and the union over the run's many queries are handled
once, generically, by the charge; they do not have to be redone here.

The disclosure set is a parameter. In the experiment it is produced by the honest signatures,
so using this bound there additionally needs the actual disclosures related to a fixed set
satisfying the load cap — that is what the leave-one-out and occupancy results are for, and
it is not done here.
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.ForsCoverageTerm

/-- The bad event: the answer parses to a digest covered by `revealed`. It does not depend
on which input was queried. -/
def CoveredAnswer (revealed : ForsCoverage.Disclosures) : Bytes → HashOutput → Prop :=
  fun _ answer => ForsCoverage.Covered revealed (MessageDigest.parse answer)

/-- A single fresh answer is covered with probability at most `2 ^ -128` under the load cap. -/
theorem prob_coveredAnswer_le (revealed : ForsCoverage.Disclosures)
    (loads : ForsCoverage.Instance → Nat)
    (hload : ∀ index tree, (revealed index tree).card ≤ loads index)
    (hmoment : ∑ index, loads index ^ 14 ≤ 2 ^ 103) (input : Bytes) :
    Pr[fun answer : HashOutput => CoveredAnswer revealed input answer |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤ 1 / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  rw [show (fun answer : HashOutput => CoveredAnswer revealed input answer) =
    ForsCoverage.Covered revealed ∘ MessageDigest.parse from rfl, ← probEvent_map]
  rw [probEvent_congr' (fun _ _ => Iff.rfl) MessageDigest.evalDist_parse_uniform]
  exact ForsCoverage.fresh_coverage_le_of_loads revealed loads hload hmoment

/-- **The FORS coverage term.** Against a disclosure set fixed in advance and satisfying the
load cap, a run whose cache grows by at most `limit` ends with a covered cached digest with
probability at most `limit / 2 ^ 128`. -/
theorem prob_coverage_within_le {α : Type} (computation : OracleComp OracleWorld α)
    (revealed : ForsCoverage.Disclosures) (loads : ForsCoverage.Instance → Nat)
    (hload : ∀ index tree, (revealed index tree).card ≤ loads index)
    (hmoment : ∑ index, loads index ^ 14 ≤ 2 ^ 103)
    (limit : Nat) (initialCache : QueryCache HashSpec)
    (hclean : GrowthCharge.CleanBad (CoveredAnswer revealed) initialCache) :
    Pr[GrowthCharge.BadWithin (CoveredAnswer revealed) initialCache limit |
      (simulateQ KeygenUniform.rom computation).run initialCache] ≤
      limit / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  refine le_of_le_of_eq
    (GrowthCharge.prob_badWithin_le computation (CoveredAnswer revealed)
      (1 / ((2 ^ 128 : Nat) : ℝ≥0∞)) limit initialCache
      (prob_coveredAnswer_le revealed loads hload hmoment) hclean) ?_
  rw [mul_one_div]

end SlhDsaSecurity.ForsCoverageTerm
