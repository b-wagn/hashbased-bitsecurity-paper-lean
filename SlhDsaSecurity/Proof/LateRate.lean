import SlhDsaSecurity.Proof.PotentialCharge
import SlhDsaSecurity.Proof.LateCharge
import SlhDsaSecurity.Proof.FramingLeak

/-!
# The ordering defect's rate

`SplitWitness.LateDisclosure` is the one way the recorder's two classes can part from the final
cache's, and `PotentialCharge.prob_fired_le` is the charge for an event of that kind. This file
is the instantiation.

The gauge is the **target recording's length**, and the potential is the entries of that
recording whose own message has no `PRF_msg` entry yet — the ones that can still be made
disclosing by an answer not yet drawn. A message-class query raises both by one; a `PRF_msg`
query at a message pays for every unit standing at that message and spends them all at once,
which is permanent by `LateCharge.not_signerRandomised_of_spent`; nothing else moves either.

So the defect costs one unit of `2 ^ -128` per entry of the target recording, which is where
the budget has room for it. It is not charged at the message class: the signer's own digests
are recorded on the disclosing side, and they are paying elsewhere.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.LateRate

open Security CacheAvailability SplitPrefix SplitWitness LateCharge ClassExpectation

/-! ## Counting a list by two tests -/

theorem length_filter_split {α : Type} (l : List α) (p q : α → Bool) :
    (l.filter (fun a => p a)).length =
      (l.filter (fun a => p a && q a)).length + (l.filter (fun a => p a && !q a)).length := by
  induction l with
  | nil => simp
  | cons head tail ih =>
    by_cases hp : p head
    · by_cases hq : q head <;> simp [hp, hq, ih] <;> omega
    · simp [hp, ih]

/-! ## The state's two numbers -/

/-- The event: some target-recorded digest is disclosing. -/
def Fired (prfSeed : Digest) (pk : PublicKey) (state : SplitState) : Prop :=
  ∃ entry ∈ state.2.2, SignerRandomised prfSeed pk state.1 entry.1

/-- The gauge: how long the target recording is. -/
def gauge (state : SplitState) : Nat := state.2.2.length

open scoped Classical in
/-- The potential: the target-recorded digests whose message has no `PRF_msg` entry yet. -/
noncomputable def potential (prfSeed : Digest) (pk : PublicKey) (state : SplitState) : Nat :=
  (state.2.2.filter (fun entry => decide (¬ Spent prfSeed pk state.1 entry.1))).length

/-- `LateDisclosure` is the event, read at the state. -/
theorem fired_iff_lateDisclosure (prfSeed : Digest) (pk : PublicKey)
    (result : (Outcome × Nat) × SplitState) :
    Fired prfSeed pk result.2 ↔ LateDisclosure prfSeed pk result := Iff.rfl

/-! ## The oracle's three steps -/

/-- Where a fresh query takes the state. -/
noncomputable def stepOf (prfSeed : Digest) (pk : PublicKey) (state : SplitState)
    (input : Bytes) (answer : HashOutput) : SplitState :=
  (state.1.cacheQuery input answer,
    appended (disclosingKeep prfSeed pk) (targetKeep prfSeed pk) input state answer)

theorem run_inl (prfSeed : Digest) (pk : PublicKey) (coin : unifSpec.Domain)
    (state : SplitState) (step : OracleWorld.Range (Sum.inl coin) × SplitState)
    (hmem : step ∈ support (((recorder (disclosingKeep prfSeed pk)
      (targetKeep prfSeed pk)) (Sum.inl coin)).run state)) : step.2 = state := by
  rw [recorder_run_inl, mem_support_bind_iff] at hmem
  obtain ⟨value, -, hpure⟩ := hmem
  rw [support_pure, Set.mem_singleton_iff] at hpure
  exact congrArg Prod.snd hpure

theorem run_inl_mass (prfSeed : Digest) (pk : PublicKey) (coin : unifSpec.Domain)
    (state : SplitState) :
    Pr[⊥ | ((recorder (disclosingKeep prfSeed pk) (targetKeep prfSeed pk))
      (Sum.inl coin)).run state] = 0 := by
  rw [recorder_run_inl]
  simp

theorem run_inr_cached (prfSeed : Digest) (pk : PublicKey) (input : Bytes) (state : SplitState)
    (answer : HashOutput) (hcached : state.1 input = some answer) :
    ((recorder (disclosingKeep prfSeed pk) (targetKeep prfSeed pk)) (Sum.inr input)).run state =
      (pure (answer, state) : ProbComp _) := by
  rw [recorder_run_inr, QueryImpl.withCaching_run_some _ hcached, pure_bind,
    appended_of_cached (disclosingKeep prfSeed pk) (targetKeep prfSeed pk) input state answer
      answer hcached]
  rfl

theorem run_inr_fresh (prfSeed : Digest) (pk : PublicKey) (input : Bytes) (state : SplitState)
    (hfresh : state.1 input = none) :
    ((recorder (disclosingKeep prfSeed pk) (targetKeep prfSeed pk)) (Sum.inr input)).run state =
      (fun answer => (answer, stepOf prfSeed pk state input answer)) <$>
        ($ᵗ HashOutput : ProbComp HashOutput) := by
  rw [recorder_run_inr, QueryImpl.withCaching_run_none _ hfresh]
  simp only [uniformSampleImpl, map_eq_bind_pure_comp, Function.comp_def,
    bind_assoc, pure_bind]
  rfl

theorem run_mass (prfSeed : Digest) (pk : PublicKey) (β : Type)
    (inner : OracleComp OracleWorld β) (state : SplitState) :
    Pr[⊥ | (simulateQ (recorder (disclosingKeep prfSeed pk) (targetKeep prfSeed pk))
      inner).run state] = 0 := by
  simp

theorem gauge_stepOf (prfSeed : Digest) (pk : PublicKey) (state : SplitState) (input : Bytes)
    (answer : HashOutput) : gauge state ≤ gauge (stepOf prfSeed pk state input answer) :=
  List.IsPrefix.length_le
    (right_prefix_appended (disclosingKeep prfSeed pk) (targetKeep prfSeed pk) input state answer)

theorem gauge_run (prfSeed : Digest) (pk : PublicKey) (β : Type)
    (inner : OracleComp OracleWorld β) (state : SplitState) (result : β × SplitState)
    (hmem : result ∈ support ((simulateQ (recorder (disclosingKeep prfSeed pk)
      (targetKeep prfSeed pk)) inner).run state)) : gauge state ≤ gauge result.2 :=
  List.IsPrefix.length_le
    (record_prefix (disclosingKeep prfSeed pk) (targetKeep prfSeed pk) inner state result hmem).2

/-! ## The potential, split by what this query settles -/

/-- A digest already settled stays settled when one more query is answered. -/
theorem becomesSpent_of_spent (prfSeed : Digest) (pk : PublicKey) (cache : QueryCache HashSpec)
    (input entry : Bytes) (hspent : Spent prfSeed pk cache entry) :
    BecomesSpent prfSeed pk cache input entry := by
  obtain ⟨message, randomizer, hentry, hpresent⟩ := hspent
  exact ⟨message, randomizer, hentry, Or.inl hpresent⟩

open scoped Classical in
/-- **The potential splits into what this query settles and what it leaves.** -/
theorem potential_split (prfSeed : Digest) (pk : PublicKey) (cache : QueryCache HashSpec)
    (input : Bytes) (record : List (Bytes × HashOutput)) :
    (record.filter (fun entry => decide (¬ Spent prfSeed pk cache entry.1))).length =
      (record.filter (fun entry => decide (¬ Spent prfSeed pk cache entry.1 ∧
          BecomesSpent prfSeed pk cache input entry.1))).length +
        (record.filter (fun entry =>
          decide (¬ BecomesSpent prfSeed pk cache input entry.1))).length := by
  classical
  rw [length_filter_split record (fun entry => decide (¬ Spent prfSeed pk cache entry.1))
    (fun entry => decide (BecomesSpent prfSeed pk cache input entry.1))]
  congr 1
  · exact congrArg List.length (List.filter_congr fun entry _ => by
      simp)
  · refine congrArg List.length (List.filter_congr fun entry _ => ?_)
    by_cases hbecomes : BecomesSpent prfSeed pk cache input entry.1
    · simp [hbecomes]
    · have hspent : ¬ Spent prfSeed pk cache entry.1 := fun hspent =>
        hbecomes (becomesSpent_of_spent prfSeed pk cache input entry.1 hspent)
      simp [hbecomes, hspent]

open scoped Classical in
/-- The potential after the query, read without the answer. -/
theorem potential_stepOf (prfSeed : Digest) (pk : PublicKey) (state : SplitState)
    (input : Bytes) (answer : HashOutput) (hfresh : state.1 input = none) :
    potential prfSeed pk (stepOf prfSeed pk state input answer) =
      ((appended (disclosingKeep prfSeed pk) (targetKeep prfSeed pk) input state answer).2.filter
        (fun entry => decide (¬ BecomesSpent prfSeed pk state.1 input entry.1))).length := by
  classical
  refine congrArg List.length (List.filter_congr fun entry _ => ?_)
  rw [show (stepOf prfSeed pk state input answer).1 = state.1.cacheQuery input answer from rfl]
  by_cases hbecomes : BecomesSpent prfSeed pk state.1 input entry.1
  · have hspent : Spent prfSeed pk (state.1.cacheQuery input answer) entry.1 :=
      (spent_cacheQuery_iff prfSeed pk state.1 input entry.1 answer hfresh).mpr hbecomes
    simp [hbecomes, hspent]
  · have hspent : ¬ Spent prfSeed pk (state.1.cacheQuery input answer) entry.1 := fun hspent =>
      hbecomes ((spent_cacheQuery_iff prfSeed pk state.1 input entry.1 answer hfresh).mp hspent)
    simp [hbecomes, hspent]

/-! ## One step of the charge

A message-class query the signer did not randomise raises both numbers by one. A query that
settles messages pays one unit for each entry it settles and spends exactly those. Nothing else
moves either number. -/

/-- The rate the defect is charged at. -/
noncomputable def rate : ℝ≥0∞ := (1 : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)

theorem rate_le {x y z w : Nat} (hle : x + y ≤ z + w) :
    ((x : Nat) : ℝ≥0∞) * rate + ((y : Nat) : ℝ≥0∞) * rate ≤
      ((z : Nat) : ℝ≥0∞) * rate + ((w : Nat) : ℝ≥0∞) * rate := by
  rw [show ((x : Nat) : ℝ≥0∞) * rate + ((y : Nat) : ℝ≥0∞) * rate =
      ((x + y : Nat) : ℝ≥0∞) * rate from by push_cast; ring,
    show ((z : Nat) : ℝ≥0∞) * rate + ((w : Nat) : ℝ≥0∞) * rate =
      ((z + w : Nat) : ℝ≥0∞) * rate from by push_cast; ring]
  exact mul_le_mul' (Nat.cast_le.mpr hle) le_rfl

theorem rate_le3 {x y z w v : Nat} (hle : x + y + z ≤ w + v) :
    ((x : Nat) : ℝ≥0∞) * rate + (((y : Nat) : ℝ≥0∞) * rate + ((z : Nat) : ℝ≥0∞) * rate) ≤
      ((w : Nat) : ℝ≥0∞) * rate + ((v : Nat) : ℝ≥0∞) * rate := by
  rw [show ((x : Nat) : ℝ≥0∞) * rate + (((y : Nat) : ℝ≥0∞) * rate + ((z : Nat) : ℝ≥0∞) * rate) =
      ((x + y + z : Nat) : ℝ≥0∞) * rate from by push_cast; ring,
    show ((w : Nat) : ℝ≥0∞) * rate + ((v : Nat) : ℝ≥0∞) * rate =
      ((w + v : Nat) : ℝ≥0∞) * rate from by push_cast; ring]
  exact mul_le_mul' (Nat.cast_le.mpr hle) le_rfl

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The step hypothesis of the potential charge, for this event.** -/
theorem step_bound (prfSeed : Digest) (pk : PublicKey) (state : SplitState) (input : Bytes)
    (hfresh : state.1 input = none) (hnotfired : ¬ Fired prfSeed pk state) :
    ∃ bound after : Nat,
      (∀ answer : HashOutput, ¬ Fired prfSeed pk (stepOf prfSeed pk state input answer) →
          potential prfSeed pk (stepOf prfSeed pk state input answer) ≤ bound) ∧
        (∀ answer : HashOutput, gauge (stepOf prfSeed pk state input answer) = after) ∧
          Pr[fun answer : HashOutput =>
              Fired prfSeed pk (stepOf prfSeed pk state input answer) |
            ($ᵗ HashOutput : ProbComp HashOutput)] + ((bound : Nat) : ℝ≥0∞) * rate ≤
            ((potential prfSeed pk state : Nat) : ℝ≥0∞) * rate +
              ((after - gauge state : Nat) : ℝ≥0∞) * rate := by
  classical
  have hnot : ∀ entry ∈ state.2.2, ¬ SignerRandomised prfSeed pk state.1 entry.1 :=
    fun entry hentry hsigner => hnotfired ⟨entry, hentry, hsigner⟩
  have hpot : potential prfSeed pk state =
      (state.2.2.filter (fun entry => decide (¬ Spent prfSeed pk state.1 entry.1 ∧
          BecomesSpent prfSeed pk state.1 input entry.1))).length +
        (state.2.2.filter (fun entry =>
          decide (¬ BecomesSpent prfSeed pk state.1 input entry.1))).length :=
    potential_split prfSeed pk state.1 input state.2.2
  have hold : Pr[fun answer : HashOutput => ∃ entry ∈ state.2.2,
        SignerRandomised prfSeed pk (state.1.cacheQuery input answer) entry.1 |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤
      (((state.2.2.filter (fun entry => decide (¬ Spent prfSeed pk state.1 entry.1 ∧
          BecomesSpent prfSeed pk state.1 input entry.1))).length : Nat) : ℝ≥0∞) * rate :=
    prob_record_fires_le prfSeed pk state.1 input state.2.2 hfresh hnot
  by_cases hleft : disclosingKeep prfSeed pk input state.1
  · refine ⟨(state.2.2.filter (fun entry =>
      decide (¬ BecomesSpent prfSeed pk state.1 input entry.1))).length, gauge state,
      fun answer _ => ?_, fun answer => ?_, ?_⟩
    · rw [potential_stepOf prfSeed pk state input answer hfresh,
        appended_of_left (disclosingKeep prfSeed pk) (targetKeep prfSeed pk) input state answer
          hfresh hleft]
    · show ((appended (disclosingKeep prfSeed pk) (targetKeep prfSeed pk) input state
        answer).2).length = state.2.2.length
      rw [appended_of_left (disclosingKeep prfSeed pk) (targetKeep prfSeed pk) input state answer
        hfresh hleft]
    · rw [hpot]
      refine le_trans (add_le_add (le_trans (probEvent_mono fun answer _ hfired => ?_) hold)
        le_rfl) (rate_le (by omega))
      obtain ⟨entry, hentry, hsigner⟩ := hfired
      refine ⟨entry, ?_, hsigner⟩
      rwa [show (stepOf prfSeed pk state input answer).2.2 =
        (appended (disclosingKeep prfSeed pk) (targetKeep prfSeed pk) input state answer).2 from
          rfl, appended_of_left (disclosingKeep prfSeed pk) (targetKeep prfSeed pk) input state
          answer hfresh hleft] at hentry
  · by_cases hright : targetKeep prfSeed pk input state.1
    · have hshape : ∀ answer : HashOutput,
          (appended (disclosingKeep prfSeed pk) (targetKeep prfSeed pk) input state answer).2 =
            state.2.2 ++ [(input, answer)] := fun answer => by
        rw [appended_of_right (disclosingKeep prfSeed pk) (targetKeep prfSeed pk) input state
          answer hfresh hleft hright]
      have hsplit : ∀ answer : HashOutput,
          Pr[fun answer : HashOutput =>
              Fired prfSeed pk (stepOf prfSeed pk state input answer) |
            ($ᵗ HashOutput : ProbComp HashOutput)] ≤
            Pr[fun answer : HashOutput => ∃ entry ∈ state.2.2,
                SignerRandomised prfSeed pk (state.1.cacheQuery input answer) entry.1 |
              ($ᵗ HashOutput : ProbComp HashOutput)] +
              Pr[fun answer : HashOutput =>
                  SignerRandomised prfSeed pk (state.1.cacheQuery input answer) input |
                ($ᵗ HashOutput : ProbComp HashOutput)] := fun _ => by
        refine le_trans (probEvent_mono (q := fun answer : HashOutput =>
          (∃ entry ∈ state.2.2,
            SignerRandomised prfSeed pk (state.1.cacheQuery input answer) entry.1) ∨
          SignerRandomised prfSeed pk (state.1.cacheQuery input answer) input)
          fun answer _ hfired => ?_) (probEvent_or_le _ _ _)
        obtain ⟨entry, hentry, hsigner⟩ := hfired
        rw [show (stepOf prfSeed pk state input answer).2.2 =
          (appended (disclosingKeep prfSeed pk) (targetKeep prfSeed pk) input state answer).2
            from rfl, hshape answer] at hentry
        rcases List.mem_append.mp hentry with hmem | hmem
        · exact Or.inl ⟨entry, hmem, hsigner⟩
        · rw [List.mem_singleton.mp hmem] at hsigner
          exact Or.inr hsigner
      by_cases hself : BecomesSpent prfSeed pk state.1 input input
      · refine ⟨(state.2.2.filter (fun entry =>
          decide (¬ BecomesSpent prfSeed pk state.1 input entry.1))).length, gauge state + 1,
          fun answer _ => ?_, fun answer => ?_, ?_⟩
        · rw [potential_stepOf prfSeed pk state input answer hfresh, hshape answer,
            List.filter_append]
          simp [hself]
        · show ((appended (disclosingKeep prfSeed pk) (targetKeep prfSeed pk) input state
            answer).2).length = state.2.2.length + 1
          rw [hshape answer]
          simp
        · rw [hpot]
          refine le_trans (add_le_add (le_trans (hsplit default)
            (add_le_add hold (prob_entry_fires_le prfSeed pk state.1 input input hright.2)))
            le_rfl) ?_
          rw [show ((1 : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)) = ((1 : Nat) : ℝ≥0∞) * rate from by
            rw [rate]; simp, add_assoc]
          exact rate_le3 (by omega)
      · refine ⟨(state.2.2.filter (fun entry =>
          decide (¬ BecomesSpent prfSeed pk state.1 input entry.1))).length + 1, gauge state + 1,
          fun answer _ => ?_, fun answer => ?_, ?_⟩
        · rw [potential_stepOf prfSeed pk state input answer hfresh, hshape answer,
            List.filter_append]
          simp [hself]
        · show ((appended (disclosingKeep prfSeed pk) (targetKeep prfSeed pk) input state
            answer).2).length = state.2.2.length + 1
          rw [hshape answer]
          simp
        · have hzero : Pr[fun answer : HashOutput =>
              SignerRandomised prfSeed pk (state.1.cacheQuery input answer) input |
            ($ᵗ HashOutput : ProbComp HashOutput)] = 0 :=
            probEvent_eq_zero fun answer _ hsigner => hself
              ((spent_cacheQuery_iff prfSeed pk state.1 input input answer hfresh).mp
                (spent_of_signerRandomised prfSeed pk _ input hsigner))
          rw [hpot]
          refine le_trans (add_le_add (le_trans (hsplit default)
            (add_le_add hold (le_of_eq hzero))) le_rfl) ?_
          rw [add_zero]
          exact rate_le (by omega)
    · refine ⟨(state.2.2.filter (fun entry =>
        decide (¬ BecomesSpent prfSeed pk state.1 input entry.1))).length, gauge state,
        fun answer _ => ?_, fun answer => ?_, ?_⟩
      · rw [potential_stepOf prfSeed pk state input answer hfresh,
          appended_of_neither (disclosingKeep prfSeed pk) (targetKeep prfSeed pk) input state
            answer hleft hright]
      · show ((appended (disclosingKeep prfSeed pk) (targetKeep prfSeed pk) input state
          answer).2).length = state.2.2.length
        rw [appended_of_neither (disclosingKeep prfSeed pk) (targetKeep prfSeed pk) input state
          answer hleft hright]
      · rw [hpot]
        refine le_trans (add_le_add (le_trans (probEvent_mono fun answer _ hfired => ?_) hold)
          le_rfl) (rate_le (by omega))
        obtain ⟨entry, hentry, hsigner⟩ := hfired
        refine ⟨entry, ?_, hsigner⟩
        rwa [show (stepOf prfSeed pk state input answer).2.2 =
          (appended (disclosingKeep prfSeed pk) (targetKeep prfSeed pk) input state answer).2 from
            rfl, appended_of_neither (disclosingKeep prfSeed pk) (targetKeep prfSeed pk) input
            state answer hleft hright] at hentry

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The ordering defect's rate.** The run holds a target-recorded digest that it later made
disclosing with probability at most one unit of `2 ^ -128` per entry of the target recording.

The count is the recording's own length, read off each run: the signer's digests are not in it,
being recorded on the disclosing side, so this is not charged at the message class. -/
theorem prob_lateDisclosure_le (prfSeed : Digest) (pk : PublicKey)
    (computation : OracleComp OracleWorld (Outcome × Nat)) (cache : QueryCache HashSpec) :
    Pr[fun result : (Outcome × Nat) × SplitState => LateDisclosure prfSeed pk result |
        (simulateQ (recorder (disclosingKeep prfSeed pk) (targetKeep prfSeed pk))
          computation).run (cache, [], [])] ≤
      expected ((simulateQ (recorder (disclosingKeep prfSeed pk) (targetKeep prfSeed pk))
          computation).run (cache, [], []))
        (fun result => result.2.2.2.length) * rate := by
  classical
  have hmain := PotentialCharge.prob_fired_le
    (recorder (disclosingKeep prfSeed pk) (targetKeep prfSeed pk))
    (fun state => state.1) (stepOf prfSeed pk)
    (run_inl prfSeed pk) (run_inl_mass prfSeed pk) (run_inr_cached prfSeed pk)
    (run_inr_fresh prfSeed pk) (run_mass prfSeed pk)
    (Fired prfSeed pk) (potential prfSeed pk) gauge rate
    (gauge_stepOf prfSeed pk) (gauge_run prfSeed pk)
    (fun state input hcache hnotfired => step_bound prfSeed pk state input hcache hnotfired)
    computation (cache, [], [])
    (by rintro ⟨entry, hentry, -⟩; simp at hentry)
  simpa [potential, gauge, Fired, LateDisclosure] using hmain

/-! ## The target recording is not the adversary's alone

The count above is the target recording's length, and the budget wants to read that as the
adversary's own message-class queries — the signer's digests being on the disclosing side,
because the signer asks `PRF_msg` before it asks `H_msg`. That reading is right for the
*digest* a served request makes. It is not right for the request's own `PRF_msg` query.

`FramingLeak.randomizerInput_eq_messageInput` is an unconditional identity of the FIPS 205
byte formats: `PRF_msg(SK.prf, PK.seed, PK.root ‖ m)` *is* `H_msg(SK.prf, PK.seed, PK.root, m)`.
So on a request framed as `PK.root ‖ m` — a legal request whenever `PK.root` begins with a zero
byte, by `FramingLeak.exists_legal_request`, which `FramingOverlap.keygen_zero_probability`
puts at exactly `1 / 256` — the signer's own `PRF_msg` query is a message-class input. It is
not signer-randomised when it is made unless the cache already holds the digest its own answer
would randomise, so the recorder files it on the target side.

The lemma below is that fact, stated at the recorder: it is not an obstruction to the charge
above, which counts whatever the target recording holds, but it is an obstruction to reading
that count as the adversary's queries alone. -/

/-- **A served request's own `PRF_msg` query can be a target-class input.** -/
theorem targetKeep_signer_randomizerInput (prfSeed : Digest) (pk : PublicKey)
    (cache : QueryCache HashSpec) (message : Bytes)
    (hnot : ¬ SignerRandomised prfSeed pk cache
      (Hashing.randomizerInput prfSeed pk.seed (bytesBE n pk.root ++ message))) :
    targetKeep prfSeed pk
      (Hashing.randomizerInput prfSeed pk.seed (bytesBE n pk.root ++ message)) cache :=
  ⟨⟨prfSeed, message, FramingLeak.randomizerInput_eq_messageInput prfSeed pk message⟩, hnot⟩

/-- The same input, read as the digest input it also is. -/
theorem signer_randomizerInput_isMessageInput (prfSeed : Digest) (pk : PublicKey)
    (message : Bytes) :
    CombinedCharge.IsMessageInput pk
      (Hashing.randomizerInput prfSeed pk.seed (bytesBE n pk.root ++ message)) :=
  ⟨prfSeed, message, FramingLeak.randomizerInput_eq_messageInput prfSeed pk message⟩

end SlhDsaSecurity.LateRate
