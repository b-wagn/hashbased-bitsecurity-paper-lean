import SlhDsaSecurity.Proof.ForsCoverageTerm
import SlhDsaSecurity.Proof.CanonicalTarget
import SlhDsaSecurity.Proof.HashSeparation

/-!
# One combined answer-side charge

Charging the structural and FORS avenues separately costs `2 ^ -128 + 2 ^ -129` per query,
which together with the `2 ^ -128` of secret guessing exceeds the target rate `2 ^ -127`. The
first-principles observation of `Proof/PerQueryBudget.lean` is that the two avenues are
*mutually exclusive by input format*: a query whose bytes are an `H_msg` input is not a
structural query, so its answer cannot hit the honest cell of a node — there is no node — and
conversely a structural query's answer is never read as a message digest.

So the two clauses should be charged as one predicate, whose per-call probability is the
**maximum** of the two rates rather than their sum:

* on a message-class input the structural clause is dead, leaving `2 ^ -129`;
* on any other input the coverage clause is dead, leaving `2 ^ -128`.

Hence `2 ^ -128` overall, and `GrowthCharge.prob_badWithin_le` then charges a whole run at
`q / 2 ^ 128 = 2q / 2 ^ 129` — half the target, leaving exactly the other half for the
secret-guessing avenue, which is the only one not of answer-side form.

The separation hypothesis `hseparated` is discharged by `Proof/HashSeparation.lean`: an
`H_msg` input can coincide with a structural one only if `PK.seed ‖ PK.root` encodes a valid
address, which has probability at most `2 ^ -165` under actual key generation.
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.CombinedCharge

open CanonicalGraph

/-- The byte inputs of the message class: those read as an `H_msg` call **under the real
public key**.

Pinning the key is not a convenience, it is required for soundness. With the key existentially
quantified an adversary could choose a `pk` whose `pk.seed ‖ pk.root` happens to encode a valid
address, craft a query that is simultaneously a message input and a structural one, and have
both clauses live at once — rate `3` on the answer side instead of `2`, which breaks the
budget. Pinning the key removes that: the only `H_msg` call that can produce a forgery is the
one the verifier makes, and the verifier uses the real key. A query under any other key is not
a message input, so the coverage clause is dead for it and only the structural clause is
charged. -/
def IsMessageInput (pk : PublicKey) (input : Bytes) : Prop :=
  ∃ (randomizer : Digest) (message : Bytes),
    input = Hashing.messageInput randomizer pk message

/-- The combined answer-side bad event: the answer either hits the honest cell of the node its
own input names, or parses to a digest already covered — the latter only on message inputs. -/
def CombinedBad (publicSeed : Digest) (pk : PublicKey) (cells : Cells)
    (revealed : ForsCoverage.Disclosures) : Bytes → HashOutput → Prop :=
  fun input answer =>
    CanonicalTarget.canonicalTarget publicSeed cells input = some (Hashing.truncate answer) ∨
      (IsMessageInput pk input ∧ ForsCoverage.Covered revealed (MessageDigest.parse answer))

open scoped Classical in
/-- **The combined per-call rate is the maximum, not the sum.** On a message input the
structural clause is dead by separation, and on any other input the coverage clause is dead by
construction, so a single fresh answer is bad with probability at most `2 ^ -128`. -/
theorem prob_combinedBad_le (publicSeed : Digest) (pk : PublicKey) (cells : Cells)
    (revealed : ForsCoverage.Disclosures) (loads : ForsCoverage.Instance → Nat)
    (hload : ∀ index tree, (revealed index tree).card ≤ loads index)
    (hmoment : ∑ index, loads index ^ 14 ≤ 2 ^ 102)
    (hseparated : ∀ input, IsMessageInput pk input →
      CanonicalTarget.canonicalTarget publicSeed cells input = none)
    (input : Bytes) :
    Pr[fun answer : HashOutput => CombinedBad publicSeed pk cells revealed input answer |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤ 1 / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  by_cases hmessage : IsMessageInput pk input
  · -- Message class: the structural clause cannot fire, so only coverage is charged.
    have hdead : ∀ answer : HashOutput,
        CombinedBad publicSeed pk cells revealed input answer →
          ForsCoverage.Covered revealed (MessageDigest.parse answer) := by
      intro answer hbad
      rcases hbad with hstructural | ⟨_, hcovered⟩
      · rw [hseparated input hmessage] at hstructural
        exact absurd hstructural (by simp)
      · exact hcovered
    refine le_trans (probEvent_mono (fun answer _ hbad => hdead answer hbad)) ?_
    refine le_trans
      (ForsCoverageTerm.prob_coveredAnswer_le_sharper revealed loads hload hmoment input) ?_
    -- `2 ^ -129 ≤ 2 ^ -128`.
    apply ENNReal.div_le_div_left
    exact_mod_cast Nat.pow_le_pow_right (by norm_num) (by norm_num)
  · -- Otherwise the coverage clause cannot fire, so only the structural target is charged.
    have hdead : ∀ answer : HashOutput,
        CombinedBad publicSeed pk cells revealed input answer →
          CanonicalTarget.canonicalTarget publicSeed cells input =
            some (Hashing.truncate answer) := by
      intro answer hbad
      rcases hbad with hstructural | ⟨hmsg, _⟩
      · exact hstructural
      · exact absurd hmsg hmessage
    refine le_trans (probEvent_mono (fun answer _ hbad => (hdead answer hbad).symm)) ?_
    exact FreshHitBound.prob_target_match_le
      (CanonicalTarget.canonicalTarget publicSeed cells input)

/-- **The answer-side half of the target.** A run whose cache grows by at most `limit`
produces a combined answer-side bad event with probability at most `limit / 2 ^ 128`, i.e.
`2 · limit / 2 ^ 129` — exactly half the target rate, charging the structural and FORS
avenues together rather than separately. -/
theorem prob_combinedBad_within_le {α : Type} (computation : OracleComp OracleWorld α)
    (publicSeed : Digest) (pk : PublicKey) (cells : Cells)
    (revealed : ForsCoverage.Disclosures)
    (loads : ForsCoverage.Instance → Nat)
    (hload : ∀ index tree, (revealed index tree).card ≤ loads index)
    (hmoment : ∑ index, loads index ^ 14 ≤ 2 ^ 102)
    (hseparated : ∀ input, IsMessageInput pk input →
      CanonicalTarget.canonicalTarget publicSeed cells input = none)
    (limit : Nat) (initialCache : QueryCache HashSpec)
    (hclean : GrowthCharge.CleanBad (CombinedBad publicSeed pk cells revealed) initialCache) :
    Pr[GrowthCharge.BadWithin (CombinedBad publicSeed pk cells revealed) initialCache limit |
      (simulateQ KeygenUniform.rom computation).run initialCache] ≤
      limit / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  refine le_of_le_of_eq
    (GrowthCharge.prob_badWithin_le computation (CombinedBad publicSeed pk cells revealed)
      (1 / ((2 ^ 128 : Nat) : ℝ≥0∞)) limit initialCache
      (prob_combinedBad_le publicSeed pk cells revealed loads hload hmoment hseparated) hclean) ?_
  rw [mul_one_div]

/-! ## Discharging the separation hypothesis

With the key pinned, `hseparated` is no longer an assumption. A structural input begins with
the real `PK.seed` and continues with an address; a message input begins with the randomizer
and continues with `PK.seed ‖ PK.root`. For one to be the other, `PK.seed ‖ PK.root` would have
to encode a valid address — `HashSeparation.Possible`, which
`HashSeparation.prob_possible_le` bounds by `2 ^ -165` for an independently uniform key pair.

The statement below is the deterministic half: given that the real key is *not* such a
coincidence, the separation holds outright, for every input and every cell assignment. -/

/-- **The separation hypothesis, discharged.** -/
theorem separated_of_not_possible (publicSeed : Digest) (pk : PublicKey) (cells : Cells)
    (hpublic : ¬ HashSeparation.Possible (pk.seed, pk.root))
    (hbounds : ∀ parent : StructuralNode, HashSeparation.WithinBounds parent.address)
    (input : Bytes) (hmessage : IsMessageInput pk input) :
    CanonicalTarget.canonicalTarget publicSeed cells input = none := by
  obtain ⟨randomizer, message, rfl⟩ := hmessage
  cases hparse : CanonicalGraph.parseInput publicSeed
      (Hashing.messageInput randomizer pk message) with
  | none => simp [CanonicalTarget.canonicalTarget, hparse]
  | some parsed =>
    exact absurd (CanonicalGraph.parseInput_sound hparse).symm
      (HashSeparation.message_tweakable_ne hpublic (hbounds parsed.parent))

end SlhDsaSecurity.CombinedCharge
