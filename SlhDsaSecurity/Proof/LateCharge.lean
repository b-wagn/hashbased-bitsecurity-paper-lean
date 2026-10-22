import SlhDsaSecurity.Proof.SplitWitness
import SlhDsaSecurity.Proof.RandomizerGate

/-!
# What the ordering defect costs, and why the payment runs backwards

`SplitWitness.LateDisclosure` is the one thing that can part the recorder's two classes from the
final cache's: a digest filed as a target, because the signer had not randomised it when it was
queried, which a later `PRF_msg` answer makes disclosing. `SplitWitness.late_ordering` says what
that means — the digest query came first, and the answer that discloses it was drawn after.

Its rate is one unit of `2 ^ -128` per message-class query, and the reason it is that rather
than one unit per `PRF_msg` query is a disjointness: a `PRF_msg` input determines its message,
so the randomisers a fresh `PRF_msg` answer could hit are the ones *already named at its own
message*, and those sets are disjoint across queries. This file carries the two facts that
disjointness rests on.

**The payment runs backwards, and that is why the existing per-query charge cannot be used.**
`ClassExpectation.prob_bad_le_expected_cost` bounds the probability of a bad answer by the
expected count of the *remaining* run, and pays for each bad step out of that step's own cost.
Here the step that can go bad is the `PRF_msg` query and the units that pay for it were spent
by message-class queries that came *before* it, which the remaining count does not mention. The
shape that does fit is a potential on the cache, carried through the induction: a message-class
query raises it by one, and a `PRF_msg` query at a message spends every unit standing at that
message at once.

`Spent` is that potential's predicate, and `not_signerRandomised_of_spent` is what makes the
spending irreversible: once the `PRF_msg` entry for a digest's message is in the cache, whether
that digest discloses is settled for good, so a unit spent at one `PRF_msg` query is never
charged again.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.LateCharge

open Security CacheAvailability

/-! ## A fresh answer lands in a named set -/

/-- **A fresh answer's truncation lands in a finite set at one unit of `2 ^ -128` per
element.** -/
theorem prob_truncate_mem_le (targets : Finset Digest) :
    Pr[fun answer : HashOutput => Hashing.truncate answer ∈ targets |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤
      (targets.card : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  calc Pr[fun answer : HashOutput => Hashing.truncate answer ∈ targets |
        ($ᵗ HashOutput : ProbComp HashOutput)]
      ≤ Pr[fun answer : HashOutput => ∃ target ∈ targets, Hashing.truncate answer = target |
          ($ᵗ HashOutput : ProbComp HashOutput)] :=
        probEvent_mono fun answer _ hmem => ⟨Hashing.truncate answer, hmem, rfl⟩
    _ ≤ ∑ target ∈ targets, Pr[fun answer : HashOutput => Hashing.truncate answer = target |
          ($ᵗ HashOutput : ProbComp HashOutput)] :=
        probEvent_exists_finset_le_sum targets _ _
    _ = ∑ _target ∈ targets, (1 : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) :=
        Finset.sum_congr rfl fun target _ => RandomizerGate.prob_truncate_eq target
    _ = (targets.card : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]

/-! ## A digest whose message already has its `PRF_msg` entry is settled -/

/-- The digest's own message already has its `PRF_msg` entry in the cache: whether this digest
discloses is decided, and the decision cannot change. -/
def Spent (prfSeed : Digest) (pk : PublicKey) (cache : QueryCache HashSpec) (input : Bytes) :
    Prop :=
  ∃ (message : Bytes) (randomizer : Digest),
    input = Hashing.messageInput randomizer pk message ∧
      cache (Hashing.randomizerInput prfSeed pk.seed message) ≠ none

/-- A signer-randomised input is settled, by its own `PRF_msg` entry. -/
theorem spent_of_signerRandomised (prfSeed : Digest) (pk : PublicKey)
    (cache : QueryCache HashSpec) (input : Bytes)
    (hsigner : SignerRandomised prfSeed pk cache input) : Spent prfSeed pk cache input := by
  obtain ⟨message, prfAnswer, hentry, hinput⟩ := hsigner
  exact ⟨message, Hashing.truncate prfAnswer, hinput, by rw [hentry]; simp⟩

/-- Settling persists: the cache only grows. -/
theorem spent_mono (prfSeed : Digest) (pk : PublicKey) {left right : QueryCache HashSpec}
    (hpersist : Persists left right) (input : Bytes) (hspent : Spent prfSeed pk left input) :
    Spent prfSeed pk right input := by
  obtain ⟨message, randomizer, hinput, hentry⟩ := hspent
  refine ⟨message, randomizer, hinput, ?_⟩
  obtain ⟨prfAnswer, hprf⟩ := Option.ne_none_iff_exists'.mp hentry
  rw [hpersist _ prfAnswer hprf]
  simp

/-- **A settled digest that does not disclose never will.** Its message's `PRF_msg` entry is
already in the cache, and entries never change, so the answer that would have to truncate to
its randomiser is fixed. This is what makes a unit spent at one `PRF_msg` query spent for
good. -/
theorem not_signerRandomised_of_spent (prfSeed : Digest) (pk : PublicKey)
    {left right : QueryCache HashSpec} (hpersist : Persists left right) (input : Bytes)
    (hspent : Spent prfSeed pk left input)
    (hnot : ¬ SignerRandomised prfSeed pk left input) :
    ¬ SignerRandomised prfSeed pk right input := by
  intro hsigner
  obtain ⟨message, randomizer, hinput, hentry⟩ := hspent
  obtain ⟨prfAnswer, hprf⟩ := Option.ne_none_iff_exists'.mp hentry
  obtain ⟨later, laterAnswer, hlater, hlaterInput⟩ := hsigner
  obtain ⟨-, -, hmessage⟩ :=
    Hashing.messageInput_injective (hinput.symm.trans hlaterInput)
  subst hmessage
  rw [hpersist _ prfAnswer hprf] at hlater
  exact hnot ⟨message, prfAnswer, hprf, by rw [hlaterInput, Option.some.inj hlater]⟩

end SlhDsaSecurity.LateCharge
