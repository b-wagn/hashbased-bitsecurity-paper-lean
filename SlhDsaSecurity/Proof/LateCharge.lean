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

/-! ## What one answer can make disclose

A digest that is not disclosing becomes disclosing only through the very entry this query
installs, so the answer has to be the `PRF_msg` answer for that digest's own message. That
pins the answer's truncation, which is why one entry costs one unit of `2 ^ -128` and no
more. -/

/-- **Firing is the new entry's doing.** -/
theorem fires_shape (prfSeed : Digest) (pk : PublicKey) (cache : QueryCache HashSpec)
    (input : Bytes) (answer : HashOutput) (entry : Bytes)
    (hnot : ¬ SignerRandomised prfSeed pk cache entry)
    (hfires : SignerRandomised prfSeed pk (cache.cacheQuery input answer) entry) :
    ∃ message : Bytes, input = Hashing.randomizerInput prfSeed pk.seed message ∧
      entry = Hashing.messageInput (Hashing.truncate answer) pk message := by
  obtain ⟨message, prfAnswer, hprf, hentry⟩ := hfires
  by_cases hsame : Hashing.randomizerInput prfSeed pk.seed message = input
  · refine ⟨message, hsame.symm, ?_⟩
    rw [hsame, QueryCache.cacheQuery_self] at hprf
    rw [hentry, Option.some.inj hprf]
  · rw [QueryCache.cacheQuery_of_ne cache answer hsame] at hprf
    exact absurd ⟨message, prfAnswer, hprf, hentry⟩ hnot

/-- **One entry costs one unit.** The answers that make a given digest disclose all have the
same truncation, so they are one fibre of a uniform draw. -/
theorem prob_entry_fires_le (prfSeed : Digest) (pk : PublicKey) (cache : QueryCache HashSpec)
    (input : Bytes) (entry : Bytes)
    (hnot : ¬ SignerRandomised prfSeed pk cache entry) :
    Pr[fun answer : HashOutput =>
        SignerRandomised prfSeed pk (cache.cacheQuery input answer) entry |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤
      (1 : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  by_cases hex : ∃ first : HashOutput,
      SignerRandomised prfSeed pk (cache.cacheQuery input first) entry
  · obtain ⟨first, hfirst⟩ := hex
    obtain ⟨firstMessage, hfirstInput, hfirstEntry⟩ :=
      fires_shape prfSeed pk cache input first entry hnot hfirst
    refine le_of_le_of_eq (probEvent_mono (q := fun answer : HashOutput =>
      Hashing.truncate answer = Hashing.truncate first) fun answer _ hfires => ?_)
      (RandomizerGate.prob_truncate_eq (Hashing.truncate first))
    obtain ⟨message, hinput, hentry⟩ :=
      fires_shape prfSeed pk cache input answer entry hnot hfires
    obtain ⟨-, -, hmessage⟩ :=
      Hashing.randomizerInput_injective (hinput.symm.trans hfirstInput)
    subst hmessage
    exact (Hashing.messageInput_injective (hentry.symm.trans hfirstEntry)).1
  · push Not at hex
    exact le_of_eq_of_le (probEvent_eq_zero fun answer _ hfires => hex answer hfires) (by simp)

/-! ## What a whole recording can lose to one answer

Only the entries this query settles can fire: one already settled is settled against disclosing,
by `not_signerRandomised_of_spent`, and one the query does not settle cannot disclose at all. So
a recording loses at most one unit of `2 ^ -128` per entry the query settles — which is the
count the potential is about to drop by. -/

/-- The digest's message is settled once this query is answered: either its `PRF_msg` entry is
already there, or this query is it. Stated without naming the answer, because the potential
must not depend on it. -/
def BecomesSpent (prfSeed : Digest) (pk : PublicKey) (cache : QueryCache HashSpec)
    (input entry : Bytes) : Prop :=
  ∃ (message : Bytes) (randomizer : Digest),
    entry = Hashing.messageInput randomizer pk message ∧
      (cache (Hashing.randomizerInput prfSeed pk.seed message) ≠ none ∨
        input = Hashing.randomizerInput prfSeed pk.seed message)

/-- A fresh query extends the cache. -/
theorem persists_cacheQuery (cache : QueryCache HashSpec) (input : Bytes)
    (answer : HashOutput) (hfresh : cache input = none) :
    Persists cache (cache.cacheQuery input answer) := by
  intro probe value hprobe
  by_cases hsame : probe = input
  · subst hsame
    rw [hfresh] at hprobe
    simp at hprobe
  · rw [QueryCache.cacheQuery_of_ne cache answer hsame]
    exact hprobe

/-- **Settled after the query, read without the answer.** -/
theorem spent_cacheQuery_iff (prfSeed : Digest) (pk : PublicKey) (cache : QueryCache HashSpec)
    (input entry : Bytes) (answer : HashOutput) (hfresh : cache input = none) :
    Spent prfSeed pk (cache.cacheQuery input answer) entry ↔
      BecomesSpent prfSeed pk cache input entry := by
  constructor
  · rintro ⟨message, randomizer, hentry, hpresent⟩
    refine ⟨message, randomizer, hentry, ?_⟩
    by_cases hsame : Hashing.randomizerInput prfSeed pk.seed message = input
    · exact Or.inr hsame.symm
    · rw [QueryCache.cacheQuery_of_ne cache answer hsame] at hpresent
      exact Or.inl hpresent
  · rintro ⟨message, randomizer, hentry, hcase⟩
    refine ⟨message, randomizer, hentry, ?_⟩
    rcases hcase with hpresent | hinput
    · obtain ⟨value, hvalue⟩ := Option.ne_none_iff_exists'.mp hpresent
      rw [persists_cacheQuery cache input answer hfresh _ value hvalue]
      simp
    · rw [← hinput, QueryCache.cacheQuery_self]
      simp

open scoped Classical in
/-- **A recording loses one unit per entry the query settles.** -/
theorem prob_record_fires_le (prfSeed : Digest) (pk : PublicKey) (cache : QueryCache HashSpec)
    (input : Bytes) (record : List (Bytes × HashOutput)) (hfresh : cache input = none)
    (hnot : ∀ entry ∈ record, ¬ SignerRandomised prfSeed pk cache entry.1) :
    Pr[fun answer : HashOutput => ∃ entry ∈ record,
        SignerRandomised prfSeed pk (cache.cacheQuery input answer) entry.1 |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤
      (((record.filter (fun entry => ¬ Spent prfSeed pk cache entry.1 ∧
            BecomesSpent prfSeed pk cache input entry.1)).length : Nat) : ℝ≥0∞) *
        ((1 : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)) := by
  classical
  refine le_trans (probEvent_mono (q := fun answer : HashOutput =>
      ∃ entry ∈ record.toFinset,
        SignerRandomised prfSeed pk (cache.cacheQuery input answer) entry.1)
    fun answer _ hfires => ?_) ?_
  · obtain ⟨entry, hentry, hsigner⟩ := hfires
    exact ⟨entry, List.mem_toFinset.mpr hentry, hsigner⟩
  refine le_trans (probEvent_exists_finset_le_sum record.toFinset _ _) ?_
  rw [← Finset.sum_filter_add_sum_filter_not record.toFinset
    (fun entry => ¬ Spent prfSeed pk cache entry.1 ∧
      BecomesSpent prfSeed pk cache input entry.1)]
  have hzero : ∑ entry ∈ record.toFinset.filter
      (fun entry => ¬ (¬ Spent prfSeed pk cache entry.1 ∧
        BecomesSpent prfSeed pk cache input entry.1)),
      Pr[fun answer : HashOutput =>
          SignerRandomised prfSeed pk (cache.cacheQuery input answer) entry.1 |
        ($ᵗ HashOutput : ProbComp HashOutput)] = 0 := by
    refine Finset.sum_eq_zero fun entry hentry => ?_
    rw [Finset.mem_filter] at hentry
    refine probEvent_eq_zero fun answer _ hsigner => ?_
    rcases not_and_or.mp hentry.2 with hspent | hbecomes
    · exact not_signerRandomised_of_spent prfSeed pk
        (persists_cacheQuery cache input answer hfresh)
        entry.1 (not_not.mp hspent)
        (hnot entry (List.mem_toFinset.mp hentry.1)) hsigner
    · exact hbecomes ((spent_cacheQuery_iff prfSeed pk cache input entry.1 answer hfresh).mp
        (spent_of_signerRandomised prfSeed pk _ entry.1 hsigner))
  rw [hzero, add_zero]
  calc ∑ entry ∈ record.toFinset.filter
        (fun entry => ¬ Spent prfSeed pk cache entry.1 ∧
          BecomesSpent prfSeed pk cache input entry.1),
        Pr[fun answer : HashOutput =>
            SignerRandomised prfSeed pk (cache.cacheQuery input answer) entry.1 |
          ($ᵗ HashOutput : ProbComp HashOutput)]
      ≤ ∑ _entry ∈ record.toFinset.filter
          (fun entry => ¬ Spent prfSeed pk cache entry.1 ∧
            BecomesSpent prfSeed pk cache input entry.1),
          (1 : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
        refine Finset.sum_le_sum fun entry hentry => ?_
        exact prob_entry_fires_le prfSeed pk cache input entry.1
          (hnot entry (List.mem_toFinset.mp (Finset.mem_filter.mp hentry).1))
    _ = ((record.toFinset.filter
          (fun entry => ¬ Spent prfSeed pk cache entry.1 ∧
            BecomesSpent prfSeed pk cache input entry.1)).card : ℝ≥0∞) *
          ((1 : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
        refine mul_le_mul' (Nat.cast_le.mpr ?_) le_rfl
        refine le_trans (Finset.card_le_card ?_) (List.toFinset_card_le _)
        intro entry hentry
        rw [Finset.mem_filter] at hentry
        exact List.mem_toFinset.mpr
          (List.mem_filter.mpr ⟨List.mem_toFinset.mp hentry.1, by simpa using hentry.2⟩)

end SlhDsaSecurity.LateCharge
