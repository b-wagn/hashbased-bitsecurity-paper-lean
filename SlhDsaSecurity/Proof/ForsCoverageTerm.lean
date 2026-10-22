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

/-! ## The sharper cap, and what it buys today

**The ledger below is `Assembly.le_target_of_terms`, which is unconsumed, and the halving it
justifies is thrown away by this file's only live consumer.** Both facts are worth stating,
because the `2 ^ 102` hypothesis is carried a long way on the strength of them.

The ledger first. It reads: the structural term costs `2q / 2 ^ 129`, the target is
`4q / 2 ^ 129`, so a FORS term of `2q / 2 ^ 129` would consume the whole budget and leave
nothing for the additive cost of relating the actual honest disclosures to a capped set; routing
FORS through the smaller load cap `2 ^ 102` of `ForsConcentrationSharper` halves it, leaving
`q / 2 ^ 129` of slack. That omits the **input side**, which costs another `2q / 2 ^ 129`, and it
is exactly the three-term accounting `Assembly.le_target_of_terms` records and `Assembly`'s own
header marks unconsumed.

Now the consumer. `CombinedCharge.prob_combinedBad_le` is the only Lean use of
`prob_coveredAnswer_le_sharper`, and it weakens `2 ^ -129` to `2 ^ -128` on the next line, with a
comment saying so. So in the live chain the `2 ^ 102` cap yields the identical `q / 2 ^ 128`
bound the weaker `2 ^ 103` cap would. The three theorems that would actually spend the halving —
`prob_coverage_within_le_sharper`, `prob_coverage_within_le_of_family`, and
`ForsCoverage.fresh_coverage_le_sharper` — have no consumers.

And `hmoment : ∑ i, loads i ^ 14 ≤ 2 ^ 102` is **never discharged**. It is carried verbatim
through `CombinedCharge` → `WholeGameStructural` → `WarmedCharges` and stops there; the live
answer path reaching `MainTheorem` carries no `hmoment` at all. It is a dead stronger hypothesis,
not a lurking one.
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

/-! ## The cap holds outright when few digests were signed

`prob_coveredAnswer_le_sharper` assumes the fourteenth-moment cap
`∑ i, loads i ^ 14 ≤ 2 ^ 102`. Establishing it in general is a concentration argument and
costs a defect of `2 ^ -126`, which the per-class assembly pays out of the message-class
slack — and that slack is `qm / 2 ^ 129`, so it covers the defect once `qm ≥ 8`.
(`2 ^ -126` is `8 / 2 ^ 129`; `Assembly.defect_eq` records the identity and `Assembly`'s own
section states the threshold correctly. The branch below is taken at `16`, which is twice what
is needed — a conservative branch point, not the threshold.)

Below `qm = 16` the cap needs no argument at all. Each message-class query discloses the
fourteen leaves of one digest, so with fewer than sixteen of them at most fifteen instances
carry any load and none carries more than fifteen. Then

    ∑ i, loads i ^ 14 ≤ 15 · 15 ^ 14 = 15 ^ 15 < 2 ^ 59 ,

comfortably inside `2 ^ 102`. So the dichotomy closes: above the threshold the slack pays for
the concentration bound, below it the cap is free. -/

/-- **The cap is free when the load is supported on few instances.** -/
theorem moment_le_of_small_support (loads : ForsCoverage.Instance → Nat)
    (carriers : Finset ForsCoverage.Instance)
    (hzero : ∀ index, index ∉ carriers → loads index = 0)
    (hsmall : carriers.card ≤ 15) (hbound : ∀ index, loads index ≤ 15) :
    ∑ index, loads index ^ 14 ≤ 2 ^ 102 := by
  classical
  have hrestrict : ∑ index, loads index ^ 14 = ∑ index ∈ carriers, loads index ^ 14 := by
    refine (Finset.sum_subset (Finset.subset_univ carriers) ?_).symm
    intro index _ hnot
    rw [hzero index hnot]
    simp
  calc ∑ index, loads index ^ 14
      = ∑ index ∈ carriers, loads index ^ 14 := hrestrict
    _ ≤ ∑ _index ∈ carriers, 15 ^ 14 :=
        Finset.sum_le_sum fun index _ => Nat.pow_le_pow_left (hbound index) 14
    _ = carriers.card * 15 ^ 14 := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 15 * 15 ^ 14 := Nat.mul_le_mul_right _ hsmall
    _ ≤ 2 ^ 102 := by norm_num

/-- The same in the form the dichotomy uses: fewer than sixteen signed digests. -/
theorem moment_le_of_few_digests (loads : ForsCoverage.Instance → Nat)
    (carriers : Finset ForsCoverage.Instance) (messageQueries : Nat)
    (hfew : messageQueries < 16)
    (hzero : ∀ index, index ∉ carriers → loads index = 0)
    (hsmall : carriers.card ≤ messageQueries)
    (hbound : ∀ index, loads index ≤ messageQueries) :
    ∑ index, loads index ^ 14 ≤ 2 ^ 102 :=
  moment_le_of_small_support loads carriers hzero
    (hsmall.trans (by omega)) (fun index => (hbound index).trans (by omega))

end SlhDsaSecurity.ForsCoverageTerm
