import SlhDsaSecurity.Proof.CoverageCount
import SlhDsaSecurity.Proof.SplitWitness

/-!
# The answer half's two charges, at the game's own tests

`CoverageCount.prob_bad_or_coverage_le_of_join` leaves three things: the join from the game's
coverage event to `BlockViews.TargetCovered`, and the two recording caps. This file supplies the
join at the game's recorder tests and the target cap from the budget. What it does not supply —
deliberately — is the narrowing's leftover.

**The leftover is not charged here and must not be.** `SplitWitness.mem_records_or_seedRandomised`
returns a disjunction: either the recordings hold the target and its witnesses, or the cache
holds a message input whose randomiser is `SK.prf`. The second is a guess at a secret the walk
drew, and these statements are read at a *fixed* walk, where that secret is already determined —
an adversary may carry it as a constant. Charging it here would be a false statement in a small
place. So it is conjoined to the event, visibly, and the shared half charges it where the seed is
still random.

The disclosing cap is likewise left as a hypothesis. It says the signer-randomised recording is
no longer than the signing limit, which is a fact about how many requests were served rather
than about this charge.

`inClass` stays a parameter, but the class it is meant at is the message class: at
`CombinedCharge.IsMessageInput pk`, the hypothesis `hrightClass` is exactly
`SplitWitness.targetKeep_class`, and `hbadClass` is the separation the structural clause is
already stated against.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.AnswerCoverage

open Security DigestTape ClassGrowth CoverageCount

/-! ## The join at the game's tests -/

open scoped Classical in
/-- **The join, with the leftover excluded rather than paid.** -/
theorem targetCovered_of_forgeryDisclosedCovered (prfSeed : Digest) (pk : PublicKey)
    (inClass : Bytes → Prop) {inside outside : QueryKind} (hne : inside ≠ outside)
    (computation : OracleComp OracleWorld Outcome) (cache : QueryCache HashSpec)
    (hfresh : ∀ input : Bytes, CombinedCharge.IsMessageInput pk input → cache input = none)
    (result : (Outcome × Counts) × SplitPrefix.SplitState)
    (hmem : result ∈ support (BlockViews.recordedRun
      (SplitWitness.disclosingKeep prfSeed pk) (SplitWitness.targetKeep prfSeed pk)
      (countQueries (splitCost inClass inside outside) computation) cache))
    (hlate : ¬ SplitWitness.LateDisclosure prfSeed pk
      ((result.1.1, result.1.2 inside + result.1.2 outside), result.2))
    (hcovered : CoverageRouted.ForgeryDisclosedCovered prfSeed pk
      ((result.1.1, result.1.2 inside + result.1.2 outside), result.2.1))
    (hseed : ¬ SplitWitness.SeedRandomised prfSeed pk result.2.1) :
    BlockViews.TargetCovered result := by
  classical
  rcases SplitWitness.mem_records_or_seedRandomised prfSeed pk (countAllHashes computation)
      cache ((result.1.1, result.1.2 inside + result.1.2 outside), result.2)
      (mem_support_recorder_countAllHashes (SplitWitness.disclosingKeep prfSeed pk)
        (SplitWitness.targetKeep prfSeed pk) inClass hne computation (cache, [], []) result hmem)
      hfresh hlate hcovered with hleftover | ⟨target, htarget, hwitness⟩
  · exact absurd hleftover hseed
  · refine ⟨target, htarget, fun tree => ?_⟩
    obtain ⟨witness, hmember, -, hinstance, hleaf⟩ := hwitness tree
    exact ⟨witness, hmember, hinstance, hleaf⟩

/-! ## Both charges, at the game's tests -/

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The answer half's two charges, against one budget.** The structural clause is paid by the
outside slot of the split counter and the coverage clause by the inside slot, so the budget
bounds their sum on every run and the bound is `budget / 2 ^ 128 + 1 / 2 ^ 141`.

The coverage clause carries `¬ SeedRandomised` with it. That is the narrowing's leftover, left
visible: the shared half charges it, where the seed the guess is against is still random. -/
theorem prob_bad_or_coverage_le_of_caps (prfSeed : Digest) (pk : PublicKey)
    (inClass : Bytes → Prop) {inside outside : QueryKind} (hne : inside ≠ outside)
    (hrightClass : ∀ (input : Bytes) (cache : QueryCache HashSpec),
      SplitWitness.targetKeep prfSeed pk input cache → inClass input)
    (bad : Bytes → HashOutput → Prop)
    (hrate : ∀ input, Pr[fun answer : HashOutput => bad input answer |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤ 1 / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hbadClass : ∀ input answer, bad input answer → ¬ inClass input)
    (computation : OracleComp OracleWorld Outcome) (initialCache : QueryCache HashSpec)
    (hclean : GrowthCharge.CleanBad bad initialCache)
    (hfresh : ∀ input : Bytes, CombinedCharge.IsMessageInput pk input →
      initialCache input = none)
    (leftLength : Nat) (hcap : leftLength ≤ 5 * 2 ^ 62)
    (hlate : ∀ result ∈ support (BlockViews.recordedRun
        (SplitWitness.disclosingKeep prfSeed pk) (SplitWitness.targetKeep prfSeed pk)
        (countQueries (splitCost inClass inside outside) computation) initialCache),
      ¬ SplitWitness.LateDisclosure prfSeed pk
        ((result.1.1, result.1.2 inside + result.1.2 outside), result.2))
    (hleftBound : ∀ result ∈ support (BlockViews.recordedRun
        (SplitWitness.disclosingKeep prfSeed pk) (SplitWitness.targetKeep prfSeed pk)
        (countQueries (splitCost inClass inside outside) computation) initialCache),
      result.2.2.1.length ≤ leftLength)
    (budget : Nat)
    (hbudget : ∀ result ∈ support ((simulateQ KeygenUniform.rom
      (countAllHashes computation)).run initialCache), result.1.2 ≤ budget) :
    Pr[fun result : (Outcome × Nat) × QueryCache HashSpec =>
        GrowthCharge.Bad bad result ∨
          (CoverageRouted.ForgeryDisclosedCovered prfSeed pk result ∧
            ¬ SplitWitness.SeedRandomised prfSeed pk result.2) |
        (simulateQ KeygenUniform.rom (countAllHashes computation)).run initialCache] ≤
      ((budget : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / 2 ^ 141 := by
  classical
  refine prob_bad_or_coverage_le_of_join inClass hne
    (SplitWitness.disclosingKeep prfSeed pk) (SplitWitness.targetKeep prfSeed pk)
    hrightClass bad hrate hbadClass computation initialCache hclean
    (fun result => CoverageRouted.ForgeryDisclosedCovered prfSeed pk result ∧
      ¬ SplitWitness.SeedRandomised prfSeed pk result.2)
    leftLength budget hcap (fun result hmem hcoverage => ?_) hleftBound
    (fun result hmem => rightRecord_length_le_budget _ _ inClass hne hrightClass computation
      initialCache result hmem budget hbudget)
    budget hbudget
  exact targetCovered_of_forgeryDisclosedCovered prfSeed pk inClass hne computation initialCache
    hfresh result hmem (hlate result hmem) hcoverage.1 hcoverage.2

/-! ## The disclosing cap

`hleftBound` says the disclosing recording is short. It is not true that every signer-randomised
entry comes from a served request — an adversary may query `messageInput (truncate (PRF …)) pk M`
itself — but to do that it first needs the `PRF_msg` answer, and acquiring *that* is either the
randomiser defect's own event or a guess at the same unit. So the honest statement is about the
`PRF_msg` class at the real seed, and that class's growth is what the shared half charges.

What is proved here is the game half, a counting argument and nothing else: each disclosing
entry is a *distinct* message input, each distinct message input needs its own `PRF_msg` entry,
so the recording is no longer than the growth in the `PRF_msg` class at the real seed. The
remaining conjunct — that growth being inside the signing limit off the defect — is the shared
half's, where the seed is still random.

The injection runs the other way from how the definition reads. `SignerRandomised` pins the
randomiser to the cached `PRF_msg` answer, so the message determines the whole input; two
distinct disclosing entries therefore have distinct messages, and distinct messages have
distinct `PRF_msg` inputs. -/

open scoped Classical in
/-- One step keeps every cached input cached. -/
theorem step_cache_mono (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (queried : OracleWorld.Domain) (state : SplitPrefix.SplitState)
    (step : OracleWorld.Range queried × SplitPrefix.SplitState)
    (hstep : step ∈ support (((SplitPrefix.recorder leftKeep rightKeep) queried).run state))
    (probe : Bytes) (hprobe : state.1 probe ≠ none) : step.2.1 probe ≠ none := by
  classical
  rcases queried with coin | input
  · rw [SplitPrefix.recorder_run_inl, mem_support_bind_iff] at hstep
    obtain ⟨value, -, hpure⟩ := hstep
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [hpure]
    exact hprobe
  · rw [SplitPrefix.recorder_run_inr, mem_support_bind_iff] at hstep
    obtain ⟨answer, hanswer, hpure⟩ := hstep
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [hpure]
    show answer.2 probe ≠ none
    cases hcached : state.1 input with
    | some value =>
      rw [QueryImpl.withCaching_run_some _ hcached, support_pure,
        Set.mem_singleton_iff] at hanswer
      rw [hanswer]
      exact hprobe
    | none =>
      rw [QueryImpl.withCaching_run_none _ hcached, support_map] at hanswer
      obtain ⟨sampled, -, hpair⟩ := hanswer
      rw [show answer.2 = state.1.cacheQuery input sampled from (Prod.ext_iff.mp hpair).2.symm]
      by_cases hsame : probe = input
      · rw [hsame, QueryCache.cacheQuery_self]
        simp
      · rw [QueryCache.cacheQuery_of_ne state.1 sampled hsame]
        exact hprobe

open scoped Classical in
/-- One step caches the input it answers. -/
theorem step_cache_queried (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (input : Bytes) (state : SplitPrefix.SplitState)
    (step : OracleWorld.Range (Sum.inr input) × SplitPrefix.SplitState)
    (hstep : step ∈ support (((SplitPrefix.recorder leftKeep rightKeep)
      (Sum.inr input)).run state)) : step.2.1 input ≠ none := by
  classical
  rw [SplitPrefix.recorder_run_inr, mem_support_bind_iff] at hstep
  obtain ⟨answer, hanswer, hpure⟩ := hstep
  rw [support_pure, Set.mem_singleton_iff] at hpure
  rw [hpure]
  show answer.2 input ≠ none
  cases hcached : state.1 input with
  | some value =>
    rw [QueryImpl.withCaching_run_some _ hcached, support_pure,
      Set.mem_singleton_iff] at hanswer
    rw [hanswer]
    show state.1 input ≠ none
    rw [hcached]
    simp
  | none =>
    rw [QueryImpl.withCaching_run_none _ hcached, support_map] at hanswer
    obtain ⟨sampled, -, hpair⟩ := hanswer
    rw [show answer.2 = state.1.cacheQuery input sampled from (Prod.ext_iff.mp hpair).2.symm,
      QueryCache.cacheQuery_self]
    simp

open scoped Classical in
/-- One step keeps every disclosing entry's input cached. -/
theorem step_leftRecord_cached (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (queried : OracleWorld.Domain) (state : SplitPrefix.SplitState)
    (step : OracleWorld.Range queried × SplitPrefix.SplitState)
    (hstep : step ∈ support (((SplitPrefix.recorder leftKeep rightKeep) queried).run state))
    (hstart : ∀ entry ∈ state.2.1, state.1 entry.1 ≠ none) :
    ∀ entry ∈ step.2.2.1, step.2.1 entry.1 ≠ none := by
  classical
  rcases queried with coin | input
  · rw [SplitPrefix.recorder_run_inl, mem_support_bind_iff] at hstep
    obtain ⟨value, -, hpure⟩ := hstep
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [hpure]
    exact hstart
  · have hgrow := step_cache_mono leftKeep rightKeep (Sum.inr input) state step hstep
    have hinput := step_cache_queried leftKeep rightKeep input state step hstep
    rw [SplitPrefix.recorder_run_inr, mem_support_bind_iff] at hstep
    obtain ⟨answer, -, hpure⟩ := hstep
    rw [support_pure, Set.mem_singleton_iff] at hpure
    intro entry hentry
    rw [hpure] at hentry
    refine (?_ : entry ∈ state.2.1 ∨ entry.1 = input).elim (fun hold => hgrow entry.1
      (hstart entry hold)) (fun hnew => by rw [hnew]; exact hinput)
    revert hentry
    show entry ∈ (SplitPrefix.appended leftKeep rightKeep input state answer.1).1 → _
    rw [SplitPrefix.appended]
    split_ifs with hleft hright
    · intro hentry
      rcases List.mem_append.mp hentry with hold | hnew
      · exact Or.inl hold
      · exact Or.inr (by simpa using congrArg Prod.fst (List.mem_singleton.mp hnew))
    · exact fun hentry => Or.inl hentry
    · exact fun hentry => Or.inl hentry

open scoped Classical in
/-- **Every disclosing entry's input is cached by the end.** -/
theorem leftRecord_cached (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    {α : Type} (computation : OracleComp OracleWorld α) :
    ∀ (state : SplitPrefix.SplitState) (result : α × SplitPrefix.SplitState),
      result ∈ support ((simulateQ (SplitPrefix.recorder leftKeep rightKeep)
        computation).run state) →
      (∀ entry ∈ state.2.1, state.1 entry.1 ≠ none) →
      ∀ entry ∈ result.2.2.1, result.2.1 entry.1 ≠ none := by
  classical
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state result hmem hstart
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [hmem]
    exact hstart
  | query_bind queried next ih =>
    intro state result hmem hstart
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    exact ih step.1 step.2 result hrest
      (step_leftRecord_cached leftKeep rightKeep queried state step hstep hstart)

open scoped Classical in
/-- **The disclosing recording files each input once.** An entry is filed only on a cache miss
and the answer is cached from then on, so no input is filed twice. -/
theorem leftRecord_nodup (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    {α : Type} (computation : OracleComp OracleWorld α) :
    ∀ (state : SplitPrefix.SplitState) (result : α × SplitPrefix.SplitState),
      result ∈ support ((simulateQ (SplitPrefix.recorder leftKeep rightKeep)
        computation).run state) →
      (∀ entry ∈ state.2.1, state.1 entry.1 ≠ none) →
      (state.2.1.map Prod.fst).Nodup →
      (result.2.2.1.map Prod.fst).Nodup := by
  classical
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state result hmem hcached hnodup
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [hmem]
    exact hnodup
  | query_bind queried next ih =>
    intro state result hmem hcached hnodup
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    refine ih step.1 step.2 result hrest
      (step_leftRecord_cached leftKeep rightKeep queried state step hstep hcached) ?_
    rcases queried with coin | input
    · rw [SplitPrefix.recorder_run_inl, mem_support_bind_iff] at hstep
      obtain ⟨value, -, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [hpure]
      exact hnodup
    · rw [SplitPrefix.recorder_run_inr, mem_support_bind_iff] at hstep
      obtain ⟨answer, -, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [hpure]
      show ((SplitPrefix.appended leftKeep rightKeep input state answer.1).1.map
        Prod.fst).Nodup
      rw [SplitPrefix.appended]
      split_ifs with hleft hright
      · rw [List.map_append]
        simp only [List.map_cons, List.map_nil]
        refine List.nodup_append.mpr ⟨hnodup, List.nodup_singleton _, ?_⟩
        intro probe hprobe other hother hsame
        obtain ⟨entry, hentry, hequal⟩ := List.mem_map.mp hprobe
        have hinput : entry.1 = input := by
          rw [hequal, hsame, List.mem_singleton.mp hother]
        exact absurd (hinput ▸ hcached entry hentry) (by rw [hleft.1]; simp)
      · exact hnodup
      · exact hnodup

/-! ### The injection into the `PRF_msg` class -/

open scoped Classical in
/-- The `PRF_msg` input behind a signer-randomised digest input. -/
noncomputable def witnessKey (prfSeed : Digest) (pk : PublicKey)
    (cache : QueryCache HashSpec) (input : Bytes) : Bytes :=
  if h : CacheAvailability.SignerRandomised prfSeed pk cache input then
    Hashing.randomizerInput prfSeed pk.seed h.choose
  else input

open scoped Classical in
/-- What the witness is, when there is one. -/
theorem witnessKey_spec (prfSeed : Digest) (pk : PublicKey) (cache : QueryCache HashSpec)
    (input : Bytes) (hsigner : CacheAvailability.SignerRandomised prfSeed pk cache input) :
    ∃ (message : Bytes) (prfAnswer : HashOutput),
      witnessKey prfSeed pk cache input = Hashing.randomizerInput prfSeed pk.seed message ∧
        cache (Hashing.randomizerInput prfSeed pk.seed message) = some prfAnswer ∧
          input = Hashing.messageInput (Hashing.truncate prfAnswer) pk message := by
  classical
  rw [witnessKey, dif_pos hsigner]
  obtain ⟨prfAnswer, hcached, hinput⟩ := hsigner.choose_spec
  exact ⟨hsigner.choose, prfAnswer, rfl, hcached, hinput⟩

open scoped Classical in
/-- The witness is a `PRF_msg` input at the real seed, and it is cached. -/
theorem witnessKey_prfClass_cached (prfSeed : Digest) (pk : PublicKey)
    (cache : QueryCache HashSpec) (input : Bytes)
    (hsigner : CacheAvailability.SignerRandomised prfSeed pk cache input) :
    RandomizerGate.PrfClass prfSeed (witnessKey prfSeed pk cache input) ∧
      cache (witnessKey prfSeed pk cache input) ≠ none := by
  obtain ⟨message, prfAnswer, hkey, hcached, -⟩ :=
    witnessKey_spec prfSeed pk cache input hsigner
  refine ⟨⟨pk.seed, message, hkey⟩, ?_⟩
  rw [hkey, hcached]
  simp

open scoped Classical in
/-- **The witness determines the input.** The randomiser is pinned to the cached `PRF_msg`
answer, so the message determines the whole digest input — which is what makes the disclosing
recording no longer than the `PRF_msg` growth. -/
theorem witnessKey_injective (prfSeed : Digest) (pk : PublicKey)
    (cache : QueryCache HashSpec) (left right : Bytes)
    (hleft : CacheAvailability.SignerRandomised prfSeed pk cache left)
    (hright : CacheAvailability.SignerRandomised prfSeed pk cache right)
    (hkey : witnessKey prfSeed pk cache left = witnessKey prfSeed pk cache right) :
    left = right := by
  obtain ⟨leftMessage, leftAnswer, hleftKey, hleftCached, hleftInput⟩ :=
    witnessKey_spec prfSeed pk cache left hleft
  obtain ⟨rightMessage, rightAnswer, hrightKey, hrightCached, hrightInput⟩ :=
    witnessKey_spec prfSeed pk cache right hright
  rw [hleftKey, hrightKey] at hkey
  obtain ⟨-, -, hmessage⟩ := Hashing.randomizerInput_injective hkey
  rw [hmessage] at hleftCached hleftInput
  rw [hleftCached] at hrightCached
  rw [hleftInput, hrightInput, Option.some_inj.mp hrightCached]

set_option maxHeartbeats 800000 in
open scoped Classical in
/-- **The disclosing recording is no longer than the `PRF_msg` growth at the real seed.** Each
entry is a distinct message input, each needs its own `PRF_msg` entry, and those entries were
not there before the run. -/
theorem leftRecord_length_le_prfGrowth (prfSeed : Digest) (pk : PublicKey)
    (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop) {α : Type}
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec)
    (result : α × SplitPrefix.SplitState)
    (hmem : result ∈ support ((simulateQ (SplitPrefix.recorder leftKeep rightKeep)
      computation).run (cache, [], [])))
    (hsigner : ∀ entry ∈ result.2.2.1,
      CacheAvailability.SignerRandomised prfSeed pk result.2.1 entry.1)
    (hprfFresh : ∀ input : Bytes, RandomizerGate.PrfClass prfSeed input → cache input = none)
    (limit : Nat)
    (hgrowth : ClassCharge.GrowthAtMostOn (RandomizerGate.PrfClass prfSeed) cache
      result.2.1 limit) :
    result.2.2.1.length ≤ limit := by
  classical
  have hnodup : (result.2.2.1.map Prod.fst).Nodup :=
    leftRecord_nodup leftKeep rightKeep computation (cache, [], []) result hmem
      (by intro entry hentry; exact absurd hentry (by simp)) (by simp)
  have hkeys := hgrowth
    ((result.2.2.1.map Prod.fst).map (witnessKey prfSeed pk result.2.1))
    (List.Nodup.map_on (fun left hleft right hright hkey => by
      obtain ⟨leftEntry, hleftEntry, hleftValue⟩ := List.mem_map.mp hleft
      obtain ⟨rightEntry, hrightEntry, hrightValue⟩ := List.mem_map.mp hright
      exact witnessKey_injective prfSeed pk result.2.1 left right
        (hleftValue ▸ hsigner leftEntry hleftEntry)
        (hrightValue ▸ hsigner rightEntry hrightEntry) hkey) hnodup)
    (fun key hkey => by
      obtain ⟨input, hinput, hvalue⟩ := List.mem_map.mp hkey
      obtain ⟨entry, hentry, hentryValue⟩ := List.mem_map.mp hinput
      obtain ⟨hclass, hcached⟩ := witnessKey_prfClass_cached prfSeed pk result.2.1 input
        (hentryValue ▸ hsigner entry hentry)
      rw [← hvalue]
      exact ⟨hclass, hprfFresh _ hclass, hcached⟩)
  simpa using hkeys

end SlhDsaSecurity.AnswerCoverage
