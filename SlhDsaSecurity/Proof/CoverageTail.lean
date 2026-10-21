import SlhDsaSecurity.Proof.DigestTape
import SlhDsaSecurity.Proof.WarmedCharges

/-!
# The FORS coverage term at the warmed tail

`DigestTape.prob_romEvent_le` charges, on any run of the shared oracle, the event that one
recorded class answer has its fourteen FORS leaves disclosed by the other recorded answers, at
one unit of `2 ^ -128` per class query. This file instantiates it at the game: the class is the
`H_msg` format, the run is `WarmedGame.tail`, and the budget is the tail's growth in that
class.

Three things have to be supplied, and each is a fact about the walk rather than about the
charge.

* **The class.** `CombinedCharge.IsMessageInput pk` is the `H_msg` format pinned at the public
  key, the same predicate the combined charge uses to separate the two answer-side clauses.
* **The freshness.** The walk programs only canonical inputs
  (`WarmedCharges.walk_cache_canonical`), and a canonical input is not a message input
  (`WarmedCharges.not_messageInput_canonical`), so no `H_msg` entry predates the tail. Every
  `H_msg` answer in the final cache was therefore drawn during the tail, and
  `DigestTape.mem_record_of_cache` puts it in the recording beside the input that asked for it.
  That is what turns a coverage statement about the *cache* into one about the *tape*.
* **The budget.** `ClassCharge.GrowthAtMostOn` is the per-class growth the charge consumes.
  `prob_coverage_tail_le` takes it as a hypothesis, so the message-class count stays separate
  from the total: the two halves of the answer side are charged against disjoint classes, and
  spending the total count on each would overspend. `prob_coverage_tail_le_of_budget` is the
  conservative instantiation at the total count, which `GrowthBudget.growth_le_count` and
  `WarmedCharges.count_le_of_budget_tail` supply from `Security.HasTotalBudget`.

The event is stated twice. `CacheCovered` is the whole coverage event — *some* message-class
cached digest is covered by the others — and is what the tape charges directly.
`ForgeryCovered` names the forgery's own digest as the covered one, which is the form the FORS
branch of the split consumes.
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.CoverageTail

open Security CanonicalGraph WarmedGame

/-! `afterSeeds` is the whole game after key generation's seeds are drawn. Nothing below takes
it apart, and left reducible it turns a defeq check between syntactically identical terms into
a full unfolding of the game. -/

attribute [local irreducible] WarmedGame.afterSeeds Scheme.keygenInternal Scheme.verify
  Scheme.sign Security.signingOracle Security.countQueries

/-! ## The event -/

/-- The digest `answer` has each of its fourteen FORS leaves also selected, at the same FORS
instance, by the digest cached at some *other* message-class input. -/
def CoveredAt (pk : PublicKey) (cache : QueryCache HashSpec) (target : Bytes)
    (answer : HashOutput) : Prop :=
  ∀ tree : MessageDigest.ForsTree, ∃ (other : Bytes) (otherAnswer : HashOutput),
    other ≠ target ∧ CombinedCharge.IsMessageInput pk other ∧
      cache other = some otherAnswer ∧
      (MessageDigest.parse otherAnswer).1 = (MessageDigest.parse answer).1 ∧
      (MessageDigest.parse otherAnswer).2 tree = (MessageDigest.parse answer).2 tree

/-- **The coverage event.** Some message-class cached digest is covered by the others. -/
def CacheCovered (pk : PublicKey) (result : (Outcome × Nat) × QueryCache HashSpec) : Prop :=
  ∃ (target : Bytes) (answer : HashOutput),
    CombinedCharge.IsMessageInput pk target ∧ result.2 target = some answer ∧
      CoveredAt pk result.2 target answer

/-- **The coverage event at the forgery's own digest.** The `H_msg` input the verifier reads
for this forgery is cached, and the digest it holds is covered by the digests of the other
message-class inputs. -/
def ForgeryCovered (pk : PublicKey) (result : (Outcome × Nat) × QueryCache HashSpec) : Prop :=
  ∃ (message : Bytes) (parsed : Signature) (answer : HashOutput),
    result.1.1.forgery.message.frame = some message ∧
      Signature.fromBytes? result.1.1.forgery.signature = some parsed ∧
        result.2 (Hashing.messageInput parsed.randomizer pk message) = some answer ∧
          CoveredAt pk result.2 (Hashing.messageInput parsed.randomizer pk message) answer

/-- The forgery's own digest being covered is a case of some digest being covered. -/
theorem cacheCovered_of_forgeryCovered (pk : PublicKey)
    (result : (Outcome × Nat) × QueryCache HashSpec) (hcovered : ForgeryCovered pk result) :
    CacheCovered pk result := by
  obtain ⟨message, parsed, answer, -, -, hentry, hcovered⟩ := hcovered
  exact ⟨_, answer, ⟨parsed.randomizer, message, rfl⟩, hentry, hcovered⟩

/-! ## No message input predates the tail

The walk programs the canonical graph and nothing else, and a canonical input is a tweakable
input, which is a different byte format from an `H_msg` input unless `PK.seed ‖ PK.root`
happens to encode a valid address. That coincidence is `HashSeparation.Possible`, assumed away
here exactly as the combined charge assumes it away. -/

/-- The walk's cache holds no message-class entry. -/
theorem walk_cache_fresh (pk : PublicKey)
    (hpublic : ¬ HashSeparation.Possible (pk.seed, pk.root))
    (hbounds : ∀ parent : StructuralNode, HashSeparation.WithinBounds parent.address)
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk) (input : Bytes)
    (hmessage : CombinedCharge.IsMessageInput pk input) : walk.2 input = none := by
  by_contra hpresent
  obtain ⟨parent, rfl⟩ := WarmedCharges.walk_cache_canonical hwalk input hpresent
  exact WarmedCharges.not_messageInput_canonical walk.1.1.2.2 walk.1.2 pk hpublic hbounds
    parent hmessage

/-! ## From the cache to the tape

Every message-class answer in the tail's final cache was drawn during the tail, so it is in the
recording with its own input beside it. A covering witness stated at the cache therefore
becomes a covering witness stated at the recording, which is what the tape charges. -/

/-- **The recording witnesses the coverage.** -/
theorem recordCovered_of_cacheCovered (adversary : Adversary) (pk : PublicKey)
    (hpublic : ¬ HashSeparation.Possible (pk.seed, pk.root))
    (hbounds : ∀ parent : StructuralNode, HashSeparation.WithinBounds parent.address)
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk)
    {result : ((Outcome × Nat) × DigestTape.RecordState)}
    (hmem : result ∈ support (DigestTape.recordedRun (CombinedCharge.IsMessageInput pk)
      (countAllHashes (afterSeeds adversary walk.1.1)) walk.2))
    (hcovered : CacheCovered pk (result.1, result.2.1)) :
    DigestTape.RecordCovered result.2.2 := by
  obtain ⟨target, answer, htargetClass, htargetEntry, hcovered⟩ := hcovered
  have hrun : result ∈ support ((simulateQ
      (DigestTape.recorder (CombinedCharge.IsMessageInput pk))
        (countAllHashes (afterSeeds adversary walk.1.1))).run (walk.2, [])) := hmem
  have hrecorded : ∀ (input : Bytes) (value : HashOutput),
      CombinedCharge.IsMessageInput pk input → result.2.1 input = some value →
        (input, value) ∈ result.2.2 := by
    intro input value hclass hentry
    exact DigestTape.mem_record_of_cache (CombinedCharge.IsMessageInput pk)
      (countAllHashes (afterSeeds adversary walk.1.1)) (walk.2, []) result hrun input value
      hclass (walk_cache_fresh pk hpublic hbounds hwalk input hclass) hentry
  refine DigestTape.recordCovered_of_witnesses result.2.2 target answer
    (hrecorded target answer htargetClass htargetEntry) fun tree => ?_
  obtain ⟨other, otherAnswer, hne, hclass, hentry, hinstance, hleaf⟩ := hcovered tree
  exact ⟨(other, otherAnswer), hrecorded other otherAnswer hclass hentry, hne,
    hinstance, hleaf⟩

/-! ## The charge -/

/-- **The FORS coverage term at the warmed tail.** With the message-class growth of the tail
bounded by `qm`, the probability that some message-class digest in the tail's final cache is
covered by the others is at most `1 / 2 ^ 141 + qm / 2 ^ 128` — one unit of `2 ^ -128` per
message-class query, which is what the budget allows the coverage clause. -/
theorem prob_cacheCovered_tail_le (adversary : Adversary) (pk : PublicKey) (qm : Nat)
    (hqm : qm ≤ 5 * 2 ^ 62)
    (hpublic : ¬ HashSeparation.Possible (pk.seed, pk.root))
    (hbounds : ∀ parent : StructuralNode, HashSeparation.WithinBounds parent.address)
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk)
    (hclass : ∀ result ∈ support (tail adversary walk),
      ClassCharge.GrowthAtMostOn (CombinedCharge.IsMessageInput pk) walk.2 result.2 qm) :
    Pr[CacheCovered pk | tail adversary walk] ≤
      (1 : ℝ≥0∞) / 2 ^ 141 + (qm : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  rw [tail]
  refine DigestTape.prob_romEvent_le (CombinedCharge.IsMessageInput pk)
    (countAllHashes (afterSeeds adversary walk.1.1)) walk.2 qm hqm (CacheCovered pk)
    fun result hmem hcovered => ⟨?_, ?_⟩
  · refine hclass (result.1, result.2.1) ?_
    rw [tail]
    exact DigestTape.mem_support_rom (CombinedCharge.IsMessageInput pk)
      (countAllHashes (afterSeeds adversary walk.1.1)) (walk.2, []) result hmem
  · exact recordCovered_of_cacheCovered adversary pk hpublic hbounds hwalk hmem hcovered

/-- **The coverage term at the forgery's own digest.** -/
theorem prob_coverage_tail_le (adversary : Adversary) (pk : PublicKey) (qm : Nat)
    (hqm : qm ≤ 5 * 2 ^ 62)
    (hpublic : ¬ HashSeparation.Possible (pk.seed, pk.root))
    (hbounds : ∀ parent : StructuralNode, HashSeparation.WithinBounds parent.address)
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk)
    (hclass : ∀ result ∈ support (tail adversary walk),
      ClassCharge.GrowthAtMostOn (CombinedCharge.IsMessageInput pk) walk.2 result.2 qm) :
    Pr[ForgeryCovered pk | tail adversary walk] ≤
      (1 : ℝ≥0∞) / 2 ^ 141 + (qm : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) :=
  le_trans (probEvent_mono fun result _ hcovered =>
      cacheCovered_of_forgeryCovered pk result hcovered)
    (prob_cacheCovered_tail_le adversary pk qm hqm hpublic hbounds hwalk hclass)

/-- **The conservative instantiation.** The charged query count bounds the growth in every
class, so the total budget already discharges the message-class hypothesis — at the cost of
spending `q` on the coverage clause, which the per-class accounting avoids. -/
theorem prob_coverage_tail_le_of_budget (adversary : Adversary) (pk : PublicKey) (q : Nat)
    (hq : q ≤ 5 * 2 ^ 62)
    (hpublic : ¬ HashSeparation.Possible (pk.seed, pk.root))
    (hbounds : ∀ parent : StructuralNode, HashSeparation.WithinBounds parent.address)
    (hbudget : HasTotalBudget adversary q)
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk) :
    Pr[ForgeryCovered pk | tail adversary walk] ≤
      (1 : ℝ≥0∞) / 2 ^ 141 + (q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  refine prob_coverage_tail_le adversary pk q hq hpublic hbounds hwalk fun result hresult => ?_
  have hgrowth : GrowthCharge.GrowthAtMost walk.2 result.2 result.1.2 := by
    refine GrowthBudget.growth_le_count (afterSeeds adversary walk.1.1) walk.2 result ?_
    rw [← tail]
    exact hresult
  exact ClassCharge.GrowthAtMostOn.of_growthAtMost
    (GrowthBudget.GrowthAtMost.mono hgrowth
      (WarmedCharges.count_le_of_budget_tail hbudget hwalk hresult))

end SlhDsaSecurity.CoverageTail
