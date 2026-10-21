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

/-! ## The sharper cap

The assembled bound needs the FORS term at `q / 2 ^ 129`, not `q / 2 ^ 128`: the structural
term already costs `2q / 2 ^ 129` and the target is `4q / 2 ^ 129`, so a FORS term of
`2q / 2 ^ 129` would consume the whole budget and leave nothing for the additive cost of
relating the actual honest disclosures to a capped set. Routing FORS through the smaller load
cap `2 ^ 102` of `ForsConcentrationSharper` halves it, leaving `q / 2 ^ 129` of slack.
-/

/-- Under the smaller load cap a single fresh answer is covered with probability at most
`2 ^ -129`. -/
theorem prob_coveredAnswer_le_sharper (revealed : ForsCoverage.Disclosures)
    (loads : ForsCoverage.Instance → Nat)
    (hload : ∀ index tree, (revealed index tree).card ≤ loads index)
    (hmoment : ∑ index, loads index ^ 14 ≤ 2 ^ 102) (input : Bytes) :
    Pr[fun answer : HashOutput => CoveredAnswer revealed input answer |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤ 1 / ((2 ^ 129 : Nat) : ℝ≥0∞) := by
  have hcount : (∑ index : ForsCoverage.Instance,
      ∏ tree : ForsCoverage.Tree, (revealed index tree).card) ≤ 2 ^ 102 := by
    refine le_trans (Finset.sum_le_sum fun index _ => ?_) hmoment
    calc
      _ ≤ ∏ _ : ForsCoverage.Tree, loads index :=
        Finset.prod_le_prod' (fun tree _ => hload index tree)
      _ = loads index ^ 14 := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rfl
  rw [show (fun answer : HashOutput => CoveredAnswer revealed input answer) =
    fun output => ForsCoverage.Covered revealed (MessageDigest.parse output) from rfl,
    ForsCoverage.fresh_digest_coverage]
  calc
    _ ≤ ((2 ^ 102 : Nat) : ℝ≥0∞) / ((2 ^ 231 : Nat) : ℝ≥0∞) :=
      ENNReal.div_le_div_right (Nat.cast_le.mpr hcount) _
    _ = _ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num

/-- **The FORS coverage term at the sharper cap.** This is the form the assembled `q / 2 ^ 127`
bound consumes. -/
theorem prob_coverage_within_le_sharper {α : Type} (computation : OracleComp OracleWorld α)
    (revealed : ForsCoverage.Disclosures) (loads : ForsCoverage.Instance → Nat)
    (hload : ∀ index tree, (revealed index tree).card ≤ loads index)
    (hmoment : ∑ index, loads index ^ 14 ≤ 2 ^ 102)
    (limit : Nat) (initialCache : QueryCache HashSpec)
    (hclean : GrowthCharge.CleanBad (CoveredAnswer revealed) initialCache) :
    Pr[GrowthCharge.BadWithin (CoveredAnswer revealed) initialCache limit |
      (simulateQ KeygenUniform.rom computation).run initialCache] ≤
      limit / ((2 ^ 129 : Nat) : ℝ≥0∞) := by
  refine le_of_le_of_eq
    (GrowthCharge.prob_badWithin_le computation (CoveredAnswer revealed)
      (1 / ((2 ^ 129 : Nat) : ℝ≥0∞)) limit initialCache
      (prob_coveredAnswer_le_sharper revealed loads hload hmoment) hclean) ?_
  rw [mul_one_div]

/-! ## Leave-one-out disclosure families

A single disclosure set cannot be used inside the experiment: the honest signer's *own*
digest is trivially covered by the very signature that disclosed it, so `CleanBad` fails for
the full set and the charge would be vacuous. The fix is that `GrowthCharge.prob_badWithin_le`
accepts an **input-dependent** bad event, so each input may be judged against its own
disclosure set — in particular against the disclosures of all *other* signatures, which is
the leave-one-out form that `ForsLeaveOneOut` is stated for.

The per-call bound is unaffected: for each fixed input the disclosure set is fixed, so the
same uniform-view computation applies. Only a uniform load cap across the family is needed.
-/

/-- The bad event for a family of disclosure sets, one per queried input. -/
def CoveredAnswerOf (revealedOf : Bytes → ForsCoverage.Disclosures) :
    Bytes → HashOutput → Prop :=
  fun input answer => ForsCoverage.Covered (revealedOf input) (MessageDigest.parse answer)

/-- **The FORS coverage term for a leave-one-out family.** Every input is judged against its
own disclosure set; a uniform load cap across the family gives the same `limit / 2 ^ 129`. -/
theorem prob_coverage_within_le_of_family {α : Type} (computation : OracleComp OracleWorld α)
    (revealedOf : Bytes → ForsCoverage.Disclosures) (loads : ForsCoverage.Instance → Nat)
    (hload : ∀ input index tree, (revealedOf input index tree).card ≤ loads index)
    (hmoment : ∑ index, loads index ^ 14 ≤ 2 ^ 102)
    (limit : Nat) (initialCache : QueryCache HashSpec)
    (hclean : GrowthCharge.CleanBad (CoveredAnswerOf revealedOf) initialCache) :
    Pr[GrowthCharge.BadWithin (CoveredAnswerOf revealedOf) initialCache limit |
      (simulateQ KeygenUniform.rom computation).run initialCache] ≤
      limit / ((2 ^ 129 : Nat) : ℝ≥0∞) := by
  refine le_of_le_of_eq
    (GrowthCharge.prob_badWithin_le computation (CoveredAnswerOf revealedOf)
      (1 / ((2 ^ 129 : Nat) : ℝ≥0∞)) limit initialCache (fun input => ?_) hclean) ?_
  · exact prob_coveredAnswer_le_sharper (revealedOf input) loads
      (fun index tree => hload input index tree) hmoment input
  · rw [mul_one_div]

end SlhDsaSecurity.ForsCoverageTerm
