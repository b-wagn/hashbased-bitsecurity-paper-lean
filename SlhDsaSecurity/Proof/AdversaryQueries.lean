import SlhDsaSecurity.Proof.StrippedGame
import SlhDsaSecurity.Proof.WarmedSplit

/-!
# The charged work never exceeds the total hash count

The input half will charge the adversary's and the verifier's own queries, and the cap it needs
on how many there are has to come from `Security.HasTotalBudget` — which bounds
`Security.countAllHashes`, the total number of hash calls anywhere in the game. What the game's
own counters report is something else: `Outcome.counts.work` is the adversary's direct calls
plus the verifier's, charged inside the run rather than around it. This file proves the
inequality between them.

It is an inequality and not an equality, for two reasons, and both are the point of the
accounting rather than slack to be removed. Key generation and the signer hash without being
charged — that is what makes the honest phase free — and a signing *request* is charged on the
`.signing` counter, which `Counts.work` does not read. So `work` is a lower bound on the total,
never an upper one.

**No hypothesis is needed.** The worry that the signing charge might collide with the work
budget does not arise: `Counts.single .signing 1` has `work = 0`, so a request contributes
nothing to the side being bounded, while the signer's hash calls contribute to the side bounding
it. The two counters measure disjoint things and the comparison is unconditional.

The proof is three inductions joined by the phase split. The adversary's phase compares the
writer its handler accumulates against the calls the whole phase makes, where the signing
oracle's sub-runs are exactly the gap. The verifier's phase compares an outer `countQueries`
against the same total, and there the two agree. Key generation charges nothing at all.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.AdversaryQueries

open Security

/-! ## Charged work, as a number -/

theorem work_add (left right : Counts) :
    (left + right).work = left.work + right.work := by
  simp only [Counts.work, Pi.add_apply]
  omega

theorem work_zero : (0 : Counts).work = 0 := rfl

theorem work_single_hash (count : Nat) : (Counts.single .hash count).work = count := by
  simp [Counts.work, Counts.single, Pi.single_eq_same, Pi.single_eq_of_ne]

theorem work_single_verification (count : Nat) :
    (Counts.single .verification count).work = count := by
  simp [Counts.work, Counts.single, Pi.single_eq_same, Pi.single_eq_of_ne]

theorem work_single_signing (count : Nat) : (Counts.single .signing count).work = 0 := by
  simp [Counts.work, Counts.single, Pi.single_eq_of_ne]

/-! ## Splitting a counted run, keeping both counts -/

theorem countAllHashes_map {α β : Type} (computation : OracleComp OracleWorld α) (f : α → β) :
    countAllHashes (f <$> computation) =
      (fun result => (f result.1, result.2)) <$> countAllHashes computation := by
  rw [map_eq_bind_pure_comp, GrowthBudget.countAllHashes_bind]
  simp only [Function.comp_def, GrowthBudget.countAllHashes_pure, pure_bind,
    map_eq_bind_pure_comp, Nat.add_zero]

/-- **A counted run factors at every sequencing point, with both counts kept.** The variant of
`WarmedSplit.mem_support_counted_bind` that remembers how the total splits. -/
theorem mem_support_counted_bind_count {α β : Type} (computation : OracleComp OracleWorld α)
    (next : α → OracleComp OracleWorld β) (cache : QueryCache HashSpec)
    (result : (β × Nat) × QueryCache HashSpec)
    (hmem : result ∈ support ((simulateQ KeygenUniform.rom
      (countAllHashes (computation >>= next))).run cache)) :
    ∃ (value : α) (middleCache : QueryCache HashSpec) (first second : Nat),
      ((value, first), middleCache) ∈ support ((simulateQ KeygenUniform.rom
        (countAllHashes computation)).run cache) ∧
      ((result.1.1, second), result.2) ∈ support ((simulateQ KeygenUniform.rom
        (countAllHashes (next value))).run middleCache) ∧
      result.1.2 = first + second := by
  rw [GrowthBudget.countAllHashes_bind, simulateQ_bind, StateT.run_bind,
    mem_support_bind_iff] at hmem
  obtain ⟨first, hfirst, hrest⟩ := hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
  obtain ⟨second, hsecond, hpure⟩ := hrest
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hpure
  refine ⟨first.1.1, first.2, first.1.2, second.1.2, hfirst, ?_, by rw [hpure]⟩
  rw [show result.1.1 = second.1.1 from by rw [hpure],
    show result.2 = second.2 from by rw [hpure]]
  exact hsecond

/-! ## The adversary's own charges -/

/-- The adversary's own oracle: forward the query to the game's world and charge the hash. -/
noncomputable def adversaryImpl : QueryImpl OracleWorld CountedRun :=
  (QueryImpl.ofLift OracleWorld (StateT SigningLog (OracleComp OracleWorld))).withAddCost
    (fun input => Counts.single .hash (hashCost input))

theorem run_counted_bind {α β : Type} (x : CountedRun α) (next : α → CountedRun β)
    (log : SigningLog) :
    (WriterT.run (x >>= next)).run log =
      (WriterT.run x).run log >>= fun outer =>
        (fun inner => ((inner.1.1, outer.1.2 * inner.1.2), inner.2)) <$>
          (WriterT.run (next outer.1.1)).run outer.2 := by
  simp only [WriterT.run_bind, StateT.run_bind, StateT.run_map]

/-- The adversary's own oracle, as the run it performs. -/
theorem run_adversaryImpl (queried : OracleWorld.Domain) (log : SigningLog) :
    ((WriterT.run (adversaryImpl queried)).run log) =
      (fun value =>
        ((value, Multiplicative.ofAdd (Counts.single .hash (hashCost queried))), log)) <$>
        (liftM (OracleWorld.query queried) : OracleComp OracleWorld (OracleWorld.Range queried)) := by
  simp only [adversaryImpl, QueryImpl.withAddCost_apply, QueryImpl.ofLift_apply, WriterT.run_bind,
    AddWriterT.run_addTell, StateT.run_bind, StateT.run_pure, pure_bind,
    StrippedGame.run_liftM_state, StateT.run_monadLift, map_eq_bind_pure_comp, bind_assoc,
    pure_bind, Function.comp_def, mul_one]

/-- **One of the adversary's own queries charges exactly what it costs.** -/
theorem work_le_count_adversaryImpl (queried : OracleWorld.Domain) (log : SigningLog)
    (cache : QueryCache HashSpec)
    (outer : (((OracleWorld.Range queried × Multiplicative Counts) × SigningLog) × Nat) ×
      QueryCache HashSpec)
    (hmem : outer ∈ support ((simulateQ KeygenUniform.rom (countAllHashes
      ((WriterT.run (adversaryImpl queried)).run log))).run cache)) :
    (Multiplicative.toAdd outer.1.1.1.2).work ≤ outer.1.2 := by
  rw [run_adversaryImpl, countAllHashes_map, GrowthBudget.countAllHashes_query, simulateQ_map,
    StateT.run_map, support_map] at hmem
  obtain ⟨inner, hinner, heq⟩ := hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hinner
  obtain ⟨step, -, hpure⟩ := hinner
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hpure
  rw [show outer.1.1.1.2 =
      Multiplicative.ofAdd (Counts.single .hash (hashCost queried)) from by rw [← heq],
    show outer.1.2 = hashCost queried from by rw [← heq, hpure]]
  simp [work_single_hash]

/-- **A signing request charges nothing to the work budget.** -/
theorem work_le_count_signingOracle (sk : SecretKey) (request : Message) (log : SigningLog)
    (cache : QueryCache HashSpec)
    (outer : (((Option Bytes × Multiplicative Counts) × SigningLog) × Nat) ×
      QueryCache HashSpec)
    (hmem : outer ∈ support ((simulateQ KeygenUniform.rom (countAllHashes
      ((WriterT.run (Security.signingOracle sk request)).run log))).run cache)) :
    (Multiplicative.toAdd outer.1.1.1.2).work ≤ outer.1.2 := by
  rw [StrippedGame.signingOracle_eq, StrippedGame.run_signingOracleWith,
    GrowthBudget.countAllHashes_bind, simulateQ_bind, StateT.run_bind,
    mem_support_bind_iff] at hmem
  obtain ⟨first, -, hrest⟩ := hmem
  rw [GrowthBudget.countAllHashes_pure, simulateQ_bind, StateT.run_bind,
    mem_support_bind_iff] at hrest
  obtain ⟨second, hsecond, hpure⟩ := hrest
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hsecond hpure
  rw [show outer.1.1.1.2 =
    Multiplicative.ofAdd (Counts.single .signing 1) from by rw [hpure, hsecond]]
  simp [work_single_signing]

set_option maxHeartbeats 1000000 in
/-- **The adversary's phase never charges more work than it makes hash calls.** The signer's
own calls are counted but not charged, so the inequality can be strict. -/
theorem work_le_count_adversary (sk : SecretKey) {α : Type}
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (log : SigningLog) (cache : QueryCache HashSpec)
      (result : (((α × Multiplicative Counts) × SigningLog) × Nat) × QueryCache HashSpec),
      result ∈ support ((simulateQ KeygenUniform.rom (countAllHashes
        ((WriterT.run (simulateQ (adversaryImpl + Security.signingOracle sk)
          computation)).run log))).run cache) →
        (Multiplicative.toAdd result.1.1.1.2).work ≤ result.1.2 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro log cache result hmem
    rw [simulateQ_pure] at hmem
    show (Multiplicative.toAdd result.1.1.1.2).work ≤ result.1.2
    rw [show ((WriterT.run (pure value : CountedRun α)).run log) =
        (pure ((value, (1 : Multiplicative Counts)), log) :
          OracleComp OracleWorld ((α × Multiplicative Counts) × SigningLog)) from rfl,
      GrowthBudget.countAllHashes_pure, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hmem
    rw [show result.1.1.1.2 = (1 : Multiplicative Counts) from by rw [hmem],
      show result.1.2 = 0 from by rw [hmem]]
    simp [work_zero]
  | query_bind queried next ih =>
    intro log cache result hmem
    rw [simulateQ_bind, simulateQ_spec_query, run_counted_bind] at hmem
    obtain ⟨outer, middleCache, first, second, houter, hinner, hsplit⟩ :=
      mem_support_counted_bind_count _ _ cache result hmem
    rw [countAllHashes_map, simulateQ_map, StateT.run_map, support_map] at hinner
    obtain ⟨inner, hinner, heq⟩ := hinner
    have htail := ih outer.1.1 outer.2 middleCache inner hinner
    have hhead : (Multiplicative.toAdd outer.1.2).work ≤ first := by
      rcases queried with world | request
      · exact work_le_count_adversaryImpl world log cache ⟨⟨outer, first⟩, middleCache⟩ houter
      · exact work_le_count_signingOracle sk request log cache ⟨⟨outer, first⟩, middleCache⟩ houter
    have hpair := congrArg Prod.fst heq
    have hvalue : result.1.1 =
        ((inner.1.1.1.1, outer.1.2 * inner.1.1.1.2), inner.1.1.2) :=
      (congrArg Prod.fst hpair).symm
    have hcount : second = inner.1.2 := (congrArg Prod.snd hpair).symm
    rw [hvalue, hsplit, hcount, toAdd_mul, work_add]
    exact Nat.add_le_add hhead htail

/-! ## The verifier's charges -/

/-- **A `Counts` instrumentation that charges one kind per hash call charges exactly the hash
calls it sees.** -/
theorem work_le_count_countQueries (kind : QueryKind) (hkind : kind ≠ .signing) {α : Type}
    (computation : OracleComp OracleWorld α) :
    ∀ (cache : QueryCache HashSpec)
      (result : ((α × Counts) × Nat) × QueryCache HashSpec),
      result ∈ support ((simulateQ KeygenUniform.rom (countAllHashes
        (countQueries (fun input => Counts.single kind (hashCost input))
          computation))).run cache) →
        (result.1.1.2).work ≤ result.1.2 := by
  have hwork : ∀ count : Nat, (Counts.single kind count).work = count := by
    intro count
    rcases kind with _ | _ | _
    · exact absurd rfl hkind
    · exact work_single_hash count
    · exact work_single_verification count
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro cache result hmem
    rw [VerificationBudget.countQueries_pure, GrowthBudget.countAllHashes_pure, simulateQ_pure,
      StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [show result.1.1.2 = 0 from by rw [hmem], show result.1.2 = 0 from by rw [hmem], work_zero]
  | query_bind queried next ih =>
    intro cache result hmem
    rw [WarmedSplit.countQueries_query_bind, GrowthBudget.countAllHashes_query_bind,
      simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, -, hrest⟩ := hmem
    rw [countAllHashes_map, simulateQ_map, StateT.run_map, support_map, simulateQ_map,
      StateT.run_map, support_map] at hrest
    obtain ⟨middle, hmiddle, hmid⟩ := hrest
    obtain ⟨inner, hinner, heq⟩ := hmiddle
    have htail := ih step.1 step.2 inner hinner
    have hvalue : result.1.1.2 = Counts.single kind (hashCost queried) + inner.1.1.2 := by
      rw [← hmid, ← heq]
    have hcount : result.1.2 = hashCost queried + inner.1.2 := by rw [← hmid, ← heq]
    rw [hvalue, hcount, work_add, hwork]
    exact Nat.add_le_add_left htail _

/-! ## The charged work of the whole game -/

attribute [local irreducible] Scheme.keygenInternal Scheme.verify Scheme.sign
  Security.signingOracle Security.countQueries

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 1000000 in
/-- **The work the game charges, plus what key generation spent, never exceeds the hash calls
the game makes.** Key generation and the signer hash without being charged, and signing requests
are charged on a counter the work budget does not read, so the inequality can be strict — and
key generation's own spend is recovered rather than discarded, which is the room the charges'
defects and the forgery's claimed cells need. -/
theorem work_add_keygen_le_total (adversary : Adversary) (sds : Digest × Digest × Digest)
    (cache : QueryCache HashSpec) (result : (Outcome × Nat) × QueryCache HashSpec)
    (hmem : result ∈ support ((simulateQ KeygenUniform.rom
      (countAllHashes (WarmedGame.afterSeeds adversary sds))).run cache)) :
    ∃ (keygenCount : Nat) (keys : SecretKey × PublicKey) (keyCache : QueryCache HashSpec),
      ((keys, keygenCount), keyCache) ∈ support ((simulateQ KeygenUniform.rom
        (countAllHashes (Scheme.keygenInternal sds.1 sds.2.1 sds.2.2))).run cache) ∧
        result.1.1.counts.work + keygenCount ≤ result.1.2 := by
  unfold WarmedGame.afterSeeds at hmem
  obtain ⟨⟨sk, pk⟩, keyCache, keyCount, advTotal, hkeys, hrest1, hsplit1⟩ :=
    mem_support_counted_bind_count _ _ cache result hmem
  refine ⟨keyCount, (sk, pk), keyCache, hkeys, ?_⟩
  obtain ⟨⟨⟨forgery, adversaryCounts⟩, signed⟩, advCache, advCount, verifyTotal, hadv, hrest2,
    hsplit2⟩ := mem_support_counted_bind_count _ _ keyCache _ hrest1
  obtain ⟨⟨verified, verifierCounts⟩, verifyCache, verifyCount, tailTotal, hverify, hrest3,
    hsplit3⟩ := mem_support_counted_bind_count _ _ advCache _ hrest2
  rw [GrowthBudget.countAllHashes_pure, simulateQ_pure, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hrest3
  have hadvWork : (Multiplicative.toAdd adversaryCounts).work ≤ advCount :=
    work_le_count_adversary sk (adversary.main pk) [] keyCache
      ⟨⟨⟨⟨forgery, adversaryCounts⟩, signed⟩, advCount⟩, advCache⟩ hadv
  have hverifyWork : verifierCounts.work ≤ verifyCount :=
    work_le_count_countQueries .verification (by decide) _ advCache
      ⟨⟨⟨verified, verifierCounts⟩, verifyCount⟩, verifyCache⟩ hverify
  have hvalue := congrArg (fun z : (Outcome × Nat) × QueryCache HashSpec => z.1.1) hrest3
  have htail := congrArg (fun z : (Outcome × Nat) × QueryCache HashSpec => z.1.2) hrest3
  simp only at hvalue htail hsplit2 hsplit3
  rw [hvalue]
  show (Multiplicative.toAdd adversaryCounts + verifierCounts).work + keyCount ≤ result.1.2
  rw [work_add, hsplit1, hsplit2, hsplit3, htail]
  omega


attribute [local irreducible] WarmedGame.afterSeeds

/-- **The work the game charges never exceeds the hash calls the game makes.** -/
theorem work_le_total (adversary : Adversary) (sds : Digest × Digest × Digest)
    (cache : QueryCache HashSpec) (result : (Outcome × Nat) × QueryCache HashSpec)
    (hmem : result ∈ support ((simulateQ KeygenUniform.rom
      (countAllHashes (WarmedGame.afterSeeds adversary sds))).run cache)) :
    result.1.1.counts.work ≤ result.1.2 := by
  obtain ⟨keygenCount, -, -, -, hbound⟩ :=
    work_add_keygen_le_total adversary sds cache result hmem
  omega

end SlhDsaSecurity.AdversaryQueries
