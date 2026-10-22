import SlhDsaSecurity.Proof.RoutedSplit
import SlhDsaSecurity.Proof.CoverageTail
import SlhDsaSecurity.Proof.AddressBounds

/-!
# The answer side, as one predicate against one budget

The target takes the answer side as a single hypothesis: one predicate, one bound. What exists
below it is two charges that were stated separately, and the reason they cannot simply be added
is the budget. Each is linear in a query count, and charging both against the whole budget
would spend `2 q / 2 ^ 128`, which is the entire target twice over.

They do not have to be. A deviating structural collision is witnessed at a *canonical* input
and the coverage event at a *message* input, and those two classes are disjoint as byte
formats as soon as the public key is no coincidence — `CombinedCharge.separated_of_not_possible`
is that separation, and `AddressBounds.withinBounds_structural` discharges the address side of
it outright, so the only hypothesis left on the key is `hpublic`.

So the structural charge is restated here against the *outside* class only: with
`ClassCharge.prob_badWithinClasses_le`, a message-class query is charged at rate zero, because
on a message input the canonical target does not exist at all. The coverage charge is already
class-counted, at the message class, by `CoverageTail.prob_coverage_tail_le`. The two counts
then add to the growth of the run rather than each equalling it, and one budget covers both.

`pk` stays free throughout. It is the real key only when the routing instantiates it, and
keeping it free here is what keeps `hpublic` a hypothesis about a public key rather than a
statement about key generation.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.AnswerSide

open Security CanonicalGraph WarmedGame

attribute [local irreducible] WarmedGame.afterSeeds Scheme.verify Scheme.keygenInternal
  Scheme.sign Security.signingOracle Security.countQueries

/-- The structural clause as a per-answer predicate: this answer hits the canonical cell of the
node its own input names, the input's child values deviating from the honest ones. -/
noncomputable def CanonicalBad (publicSeed : Digest) (cells : Cells) :
    Bytes → HashOutput → Prop :=
  fun input answer =>
    CanonicalTarget.canonicalTarget publicSeed cells input = some (Hashing.truncate answer)

/-- **On a message input there is nothing to hit.** The canonical target is `none` there, the
public key being no coincidence, so a message-class query is charged at rate zero. -/
theorem prob_canonicalBad_message_eq_zero (publicSeed : Digest) (pk : PublicKey) (cells : Cells)
    (hpublic : ¬ HashSeparation.Possible (pk.seed, pk.root))
    (input : Bytes) (hmessage : CombinedCharge.IsMessageInput pk input) :
    Pr[fun answer : HashOutput => CanonicalBad publicSeed cells input answer |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤ 0 := by
  refine le_of_eq (probEvent_eq_zero fun answer _ hbad => ?_)
  rw [CanonicalBad, CombinedCharge.separated_of_not_possible publicSeed pk cells hpublic
    withinBounds_structural input hmessage] at hbad
  exact absurd hbad (by simp)

/-- **Off the message class the rate is one unit of `2 ^ -128`.** -/
theorem prob_canonicalBad_le (publicSeed : Digest) (cells : Cells) (input : Bytes) :
    Pr[fun answer : HashOutput => CanonicalBad publicSeed cells input answer |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤ 1 / ((2 ^ 128 : Nat) : ℝ≥0∞) :=
  le_trans (probEvent_mono fun _ _ hbad => hbad.symm)
    (FreshHitBound.prob_target_match_le (CanonicalTarget.canonicalTarget publicSeed cells input))

set_option maxHeartbeats 1000000 in
/-- **The structural term, charged on the class it lives in.** The collision is witnessed at a
canonical input, so only the queries outside the message class pay for it. -/
theorem prob_deviatingCollision_outside_le (adversary : Adversary) (pk : PublicKey)
    (qs qm : Nat) (hpublic : ¬ HashSeparation.Possible (pk.seed, pk.root))
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk)
    (hinside : ∀ result ∈ support (tail adversary walk),
      ClassCharge.GrowthAtMostOn (CombinedCharge.IsMessageInput pk) walk.2 result.2 qm)
    (houtside : ∀ result ∈ support (tail adversary walk),
      ClassCharge.GrowthAtMostOn (fun input => ¬ CombinedCharge.IsMessageInput pk input)
        walk.2 result.2 qs) :
    Pr[fun result : (Outcome × Nat) × QueryCache HashSpec =>
        StructuralTerm.DeviatingCollision walk.1.1.2.2 walk.1.2 result | tail adversary walk] ≤
      (qs : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  have hcharge := ClassCharge.prob_badWithinClasses_le
    (countAllHashes (afterSeeds adversary walk.1.1))
    (CanonicalBad walk.1.1.2.2 walk.1.2) (CombinedCharge.IsMessageInput pk)
    0 (1 / ((2 ^ 128 : Nat) : ℝ≥0∞)) qm qs walk.2
    (fun input hmessage => prob_canonicalBad_message_eq_zero walk.1.1.2.2 pk walk.1.2 hpublic
      input hmessage)
    (fun input _ => prob_canonicalBad_le walk.1.1.2.2 walk.1.2 input)
    (CanonicalTarget.clean_of_canonical_cache walk.1.1.2.2 walk.1.2 walk.2
      (WarmedCharges.walk_cache_canonical hwalk))
  rw [mul_zero, zero_add, mul_one_div] at hcharge
  rw [tail]
  refine le_trans (probEvent_mono ?_) hcharge
  rintro result hresult ⟨candidates, parent, output, hdeviates, hentry, hcollision⟩
  have hres : result ∈ support (tail adversary walk) := by rw [tail]; exact hresult
  exact ⟨CanonicalTarget.hit_of_deviating_collision walk.1.1.2.2 walk.1.2 candidates parent
    result output hdeviates hentry hcollision, hinside result hres, houtside result hres⟩

end SlhDsaSecurity.AnswerSide
