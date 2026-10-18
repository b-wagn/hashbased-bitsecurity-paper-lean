import XmssSecurity.Proof.TargetSum.Direct.SignerRace

/-!
# Counting cached encoding inputs at an epoch

The collision potential reads three counts off the random-oracle cache at an epoch: the cached
encoding inputs (`entries`), those whose digest decodes (`validEntries`), and those whose digest
decodes and is shared by another cached encoding input of the epoch (`partneredEntries`). A
fresh query at the epoch adds one entry, which is decodable exactly when its digest is, and
raises the partnered count by at most `2`, and only if its digest equals a decodable cached
digest (`partneredEntries_cacheQuery_subset`).
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Direct.Collision

variable (parameter : PublicParameter) (cache : QueryCache HashSpec) (leafIndex : LeafIndex)

/-- The encoding input of a message–randomizer pair at the epoch. -/
abbrev input (entry : Message × Randomness) : HashInput :=
  Concrete.CacheView.encodingInput parameter leafIndex entry

/-- The cached encoding inputs at the epoch. -/
def entries : Set (Message × Randomness) :=
  {entry | cache (input parameter leafIndex entry) ≠ none}

/-- A cached encoding input whose digest decodes. -/
def IsValid (entry : Message × Randomness) : Prop :=
  ∃ output, cache (input parameter leafIndex entry) = some output ∧
    TargetSum.ValidDigest (truncateHash output)

/-- A cached decodable encoding input whose digest another cached encoding input of the epoch
shares. -/
def IsPartnered (entry : Message × Randomness) : Prop :=
  ∃ output, cache (input parameter leafIndex entry) = some output ∧
    TargetSum.ValidDigest (truncateHash output) ∧
    ∃ other ≠ entry, ∃ otherOutput, cache (input parameter leafIndex other) = some otherOutput ∧
      truncateHash otherOutput = truncateHash output

def validEntries : Set (Message × Randomness) := {entry | IsValid parameter cache leafIndex entry}

def partneredEntries : Set (Message × Randomness) :=
  {entry | IsPartnered parameter cache leafIndex entry}

/-- The decodable cached randomizers for one message. -/
noncomputable def validRandomizers (message : Message) : Finset Randomness := by
  classical
  exact Finset.univ.filter (DecodableAt parameter leafIndex message cache)

/-- The decodable digests cached at the epoch. -/
noncomputable def validDigests : Set Digest :=
  (fun entry => truncateHash ((cache (input parameter leafIndex entry)).getD 0)) ''
    validEntries parameter cache leafIndex

variable {parameter cache leafIndex}

theorem mem_entries {entry : Message × Randomness} :
    entry ∈ entries parameter cache leafIndex ↔ cache (input parameter leafIndex entry) ≠ none :=
  Iff.rfl

theorem mem_validEntries {entry : Message × Randomness} :
    entry ∈ validEntries parameter cache leafIndex ↔ IsValid parameter cache leafIndex entry :=
  Iff.rfl

theorem mem_partneredEntries {entry : Message × Randomness} :
    entry ∈ partneredEntries parameter cache leafIndex ↔
      IsPartnered parameter cache leafIndex entry := Iff.rfl

theorem IsPartnered.isValid {entry : Message × Randomness}
    (h : IsPartnered parameter cache leafIndex entry) : IsValid parameter cache leafIndex entry := by
  obtain ⟨output, hcache, hvalid, _⟩ := h
  exact ⟨output, hcache, hvalid⟩

theorem IsValid.mem_entries {entry : Message × Randomness}
    (h : IsValid parameter cache leafIndex entry) : entry ∈ entries parameter cache leafIndex := by
  obtain ⟨output, hcache, _⟩ := h
  show cache (input parameter leafIndex entry) ≠ none
  rw [hcache]
  exact Option.some_ne_none _

theorem partneredEntries_subset_valid :
    partneredEntries parameter cache leafIndex ⊆ validEntries parameter cache leafIndex :=
  fun _ hentry => mem_validEntries.mpr (mem_partneredEntries.mp hentry).isValid

theorem validEntries_subset_entries :
    validEntries parameter cache leafIndex ⊆ entries parameter cache leafIndex :=
  fun _ hentry => (mem_validEntries.mp hentry).mem_entries

theorem card_validRandomizers_le_ncard_validEntries (message : Message) :
    (validRandomizers parameter cache leafIndex message).card ≤
      (validEntries parameter cache leafIndex).ncard := by
  classical
  rw [← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard_of_injOn (fun randomness => (message, randomness)) ?_ ?_
  · intro randomness hrandomness
    simp only [validRandomizers, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq] at hrandomness
    exact mem_validEntries.mpr hrandomness
  · intro left _ right _ heq
    exact congrArg Prod.snd heq

theorem card_cachedRandomizersAt_le_ncard_entries (message : Message) :
    (cachedRandomizersAt parameter leafIndex message cache).card ≤
      (entries parameter cache leafIndex).ncard := by
  classical
  rw [← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard_of_injOn (fun randomness => (message, randomness)) ?_ ?_
  · intro randomness hrandomness
    simp only [cachedRandomizersAt, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq] at hrandomness
    exact mem_entries.mpr hrandomness
  · intro left _ right _ heq
    exact congrArg Prod.snd heq

theorem validRandomizers_subset_cached (message : Message) :
    validRandomizers parameter cache leafIndex message ⊆
      cachedRandomizersAt parameter leafIndex message cache := by
  classical
  intro randomness hrandomness
  simp only [validRandomizers, Finset.mem_filter, Finset.mem_univ, true_and] at hrandomness
  exact hrandomness.mem_cached

theorem ncard_validDigests_le :
    (validDigests parameter cache leafIndex).ncard ≤
      (validEntries parameter cache leafIndex).ncard :=
  Set.ncard_image_le (Set.toFinite _)

/-! ### Other epochs and other inputs -/

theorem input_ne_of_leafIndex_ne {leafIndex' : LeafIndex} (hne : leafIndex' ≠ leafIndex)
    (entry entry' : Message × Randomness) :
    input parameter leafIndex' entry' ≠ input parameter leafIndex entry := fun heq =>
  hne (Concrete.CacheView.leafIndex_eq_of_encodingInput_eq parameter heq)

/-- Counts at an epoch depend only on the cache at that epoch's encoding inputs. -/
theorem stats_congr {cache' : QueryCache HashSpec}
    (h : ∀ entry, cache' (input parameter leafIndex entry) = cache (input parameter leafIndex entry)) :
    entries parameter cache' leafIndex = entries parameter cache leafIndex ∧
      validEntries parameter cache' leafIndex = validEntries parameter cache leafIndex ∧
      partneredEntries parameter cache' leafIndex = partneredEntries parameter cache leafIndex ∧
      (∀ message, cachedRandomizersAt parameter leafIndex message cache' =
        cachedRandomizersAt parameter leafIndex message cache) ∧
      (∀ message, validRandomizers parameter cache' leafIndex message =
        validRandomizers parameter cache leafIndex message) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext entry; simp only [mem_entries, h]
  · ext entry; simp only [mem_validEntries, IsValid, h]
  · ext entry; simp only [mem_partneredEntries, IsPartnered, h]
  · intro message; ext randomness
    simp only [cachedRandomizersAt, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Iff.of_eq (congrArg (· ≠ none) (h (message, randomness)))
  · intro message; ext randomness
    simp only [validRandomizers, Finset.mem_filter, Finset.mem_univ, true_and, DecodableAt]
    rw [show Concrete.CacheView.encodingInput parameter leafIndex (message, randomness) =
      input parameter leafIndex (message, randomness) from rfl, h]

/-! ### A fresh query at the epoch -/

section Fresh

variable (fresh : Message × Randomness) (output : HashOutput)

omit cache in
theorem cacheQuery_input_self (cache : QueryCache HashSpec) :
    (cache.cacheQuery (input parameter leafIndex fresh) output) (input parameter leafIndex fresh) =
      some output := by
  simp

omit cache in
theorem cacheQuery_input_other (cache : QueryCache HashSpec) {entry : Message × Randomness}
    (hne : entry ≠ fresh) :
    (cache.cacheQuery (input parameter leafIndex fresh) output) (input parameter leafIndex entry) =
      cache (input parameter leafIndex entry) := by
  refine QueryCache.cacheQuery_of_ne _ _ fun heq => hne ?_
  exact Concrete.CacheView.encodingInput_injective parameter leafIndex heq

variable (hfresh : cache (input parameter leafIndex fresh) = none)
include hfresh

theorem fresh_not_mem_entries : fresh ∉ entries parameter cache leafIndex := by
  rw [mem_entries, hfresh]
  simp

theorem entries_cacheQuery :
    entries parameter (cache.cacheQuery (input parameter leafIndex fresh) output) leafIndex =
      insert fresh (entries parameter cache leafIndex) := by
  ext entry
  by_cases hentry : entry = fresh
  · subst hentry
    simp [mem_entries]
  · rw [Set.mem_insert_iff, mem_entries, mem_entries,
      cacheQuery_input_other (parameter := parameter) (leafIndex := leafIndex) fresh output cache hentry]
    simp [hentry]

theorem ncard_entries_cacheQuery :
    (entries parameter (cache.cacheQuery (input parameter leafIndex fresh) output)
      leafIndex).ncard = (entries parameter cache leafIndex).ncard + 1 := by
  rw [entries_cacheQuery fresh output hfresh,
    Set.ncard_insert_of_notMem (fresh_not_mem_entries fresh hfresh)]

theorem validEntries_cacheQuery :
    validEntries parameter (cache.cacheQuery (input parameter leafIndex fresh) output)
        leafIndex =
      if TargetSum.ValidDigest (truncateHash output) then
        insert fresh (validEntries parameter cache leafIndex)
      else validEntries parameter cache leafIndex := by
  ext entry
  by_cases hentry : entry = fresh
  · subst hentry
    have hnot : entry ∉ validEntries parameter cache leafIndex := fun hmem =>
      fresh_not_mem_entries entry hfresh (validEntries_subset_entries hmem)
    by_cases hvalid : TargetSum.ValidDigest (truncateHash output)
    · simp only [hvalid, if_true, Set.mem_insert_iff, true_or, iff_true]
      exact mem_validEntries.mpr ⟨output, cacheQuery_input_self (parameter := parameter) (leafIndex := leafIndex) entry output cache, hvalid⟩
    · simp only [hvalid, if_false, hnot, iff_false]
      rw [mem_validEntries]
      rintro ⟨found, hfound, hfoundValid⟩
      rw [cacheQuery_input_self (parameter := parameter) (leafIndex := leafIndex) entry output cache, Option.some.injEq] at hfound
      subst hfound
      exact hvalid hfoundValid
  · have hcache := cacheQuery_input_other (parameter := parameter) (leafIndex := leafIndex) fresh output cache hentry
    have hiff : IsValid parameter (cache.cacheQuery (input parameter leafIndex fresh) output)
        leafIndex entry ↔ IsValid parameter cache leafIndex entry := by
      simp only [IsValid, hcache]
    split_ifs <;> simp [Set.mem_insert_iff, hentry, mem_validEntries, hiff]

theorem ncard_validEntries_cacheQuery :
    ((validEntries parameter (cache.cacheQuery (input parameter leafIndex fresh) output)
      leafIndex).ncard : ℝ) = (validEntries parameter cache leafIndex).ncard +
        if TargetSum.ValidDigest (truncateHash output) then 1 else 0 := by
  rw [validEntries_cacheQuery fresh output hfresh]
  split_ifs
  · rw [Set.ncard_insert_of_notMem (fun hmem =>
      fresh_not_mem_entries fresh hfresh (validEntries_subset_entries hmem))]
    push_cast
    rfl
  · simp

theorem card_validRandomizers_cacheQuery_self :
    ((validRandomizers parameter (cache.cacheQuery (input parameter leafIndex fresh) output)
      leafIndex fresh.1).card : ℝ) = (validRandomizers parameter cache leafIndex fresh.1).card +
        if TargetSum.ValidDigest (truncateHash output) then 1 else 0 := by
  classical
  have hset : validRandomizers parameter (cache.cacheQuery (input parameter leafIndex fresh) output)
      leafIndex fresh.1 = if TargetSum.ValidDigest (truncateHash output) then
        insert fresh.2 (validRandomizers parameter cache leafIndex fresh.1)
      else validRandomizers parameter cache leafIndex fresh.1 := by
    have hvalidSet := validEntries_cacheQuery fresh output hfresh
    have hmemV : ∀ (c : QueryCache HashSpec) randomness,
        randomness ∈ validRandomizers parameter c leafIndex fresh.1 ↔
          (fresh.1, randomness) ∈ validEntries parameter c leafIndex := by
      intro c randomness
      simp only [validRandomizers, Finset.mem_filter, Finset.mem_univ, true_and]
      rfl
    ext randomness
    rw [hmemV, hvalidSet]
    by_cases hr : randomness = fresh.2
    · subst hr
      have hpair : (fresh.1, fresh.2) = fresh := rfl
      rw [hpair]
      have hnot : fresh ∉ validEntries parameter cache leafIndex := fun hmem =>
        fresh_not_mem_entries fresh hfresh (validEntries_subset_entries hmem)
      split_ifs
      · simp
      · rw [hmemV, hpair]
    · have hne : (fresh.1, randomness) ≠ fresh := fun heq => hr (congrArg Prod.snd heq)
      split_ifs
      · rw [Set.mem_insert_iff, Finset.mem_insert, hmemV]
        simp [hne, hr]
      · rw [hmemV]
  rw [hset]
  split_ifs
  · rw [Finset.card_insert_of_notMem]
    · push_cast; ring
    · intro hmem
      simp only [validRandomizers, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      obtain ⟨found, hfound, _⟩ := hmem
      have hfound' : cache (input parameter leafIndex fresh) = some found := hfound
      rw [hfresh] at hfound'
      simp at hfound'
  · simp only [add_zero]

theorem validRandomizers_cacheQuery_other {message : Message} (hne : message ≠ fresh.1) :
    validRandomizers parameter (cache.cacheQuery (input parameter leafIndex fresh) output)
        leafIndex message = validRandomizers parameter cache leafIndex message := by
  classical
  ext randomness
  have hentry : (message, randomness) ≠ fresh := fun heq => hne (congrArg Prod.fst heq)
  simp only [validRandomizers, Finset.mem_filter, Finset.mem_univ, true_and, DecodableAt]
  rw [show Concrete.CacheView.encodingInput parameter leafIndex (message, randomness) =
    input parameter leafIndex (message, randomness) from rfl,
    cacheQuery_input_other (parameter := parameter) (leafIndex := leafIndex) fresh output cache hentry]

theorem cachedRandomizersAt_cacheQuery_other {message : Message} (hne : message ≠ fresh.1) :
    cachedRandomizersAt parameter leafIndex message
        (cache.cacheQuery (input parameter leafIndex fresh) output) =
      cachedRandomizersAt parameter leafIndex message cache := by
  classical
  ext randomness
  have hentry : (message, randomness) ≠ fresh := fun heq => hne (congrArg Prod.fst heq)
  simp only [cachedRandomizersAt, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [show Concrete.CacheView.encodingInput parameter leafIndex (message, randomness) =
    input parameter leafIndex (message, randomness) from rfl,
    cacheQuery_input_other (parameter := parameter) (leafIndex := leafIndex) fresh output cache hentry]

open Classical in
/-- After a fresh query, the partnered entries are the old ones, the fresh entry, and at most
one previously unpartnered entry sharing its digest; nothing new unless the fresh digest equals
a cached decodable digest. -/
theorem ncard_partneredEntries_cacheQuery_le :
    ((partneredEntries parameter (cache.cacheQuery (input parameter leafIndex fresh) output)
      leafIndex).ncard : ℝ) ≤ (partneredEntries parameter cache leafIndex).ncard +
        if truncateHash output ∈ validDigests parameter cache leafIndex then 2 else 0 := by
  set cache' := cache.cacheQuery (input parameter leafIndex fresh) output with hcache'
  set old := partneredEntries parameter cache leafIndex
  set shared : Set (Message × Randomness) := {entry | entry ∈ validEntries parameter cache leafIndex ∧
    truncateHash ((cache (input parameter leafIndex entry)).getD 0) = truncateHash output ∧
      entry ∉ old}
  have hsub : partneredEntries parameter cache' leafIndex ⊆ old ∪ insert fresh shared := by
    intro entry hentry
    rw [mem_partneredEntries] at hentry
    obtain ⟨found, hfound, hvalid, other, hother, otherOutput, hotherCache, hsame⟩ := hentry
    by_cases hentryFresh : entry = fresh
    · exact Or.inr (Set.mem_insert_iff.mpr (Or.inl hentryFresh))
    rw [hcache', cacheQuery_input_other (parameter := parameter) (leafIndex := leafIndex) fresh output cache hentryFresh] at hfound
    by_cases hold : entry ∈ old
    · exact Or.inl hold
    refine Or.inr (Set.mem_insert_iff.mpr (Or.inr ?_))
    refine ⟨mem_validEntries.mpr ⟨found, hfound, hvalid⟩, ?_, hold⟩
    rw [hfound, Option.getD_some]
    by_cases hotherFresh : other = fresh
    · rw [hotherFresh, hcache', cacheQuery_input_self (parameter := parameter)
        (leafIndex := leafIndex) fresh output cache, Option.some.injEq] at hotherCache
      rw [hotherCache]
      exact hsame.symm
    · exfalso
      rw [hcache', cacheQuery_input_other (parameter := parameter) (leafIndex := leafIndex) fresh output cache hotherFresh] at hotherCache
      exact hold (mem_partneredEntries.mpr
        ⟨found, hfound, hvalid, other, hother, otherOutput, hotherCache, hsame⟩)
  have hone : shared.ncard ≤ 1 := by
    rw [Set.ncard_le_one]
    intro left hleft right hright
    by_contra hne
    obtain ⟨leftFound, hleftCache, hleftValid⟩ := mem_validEntries.mp hleft.1
    obtain ⟨rightFound, hrightCache, _⟩ := mem_validEntries.mp hright.1
    apply hleft.2.2
    refine mem_partneredEntries.mpr ⟨leftFound, hleftCache, hleftValid, right, fun h => hne h.symm,
      rightFound, hrightCache, ?_⟩
    have hl := hleft.2.1
    have hr := hright.2.1
    rw [hleftCache, Option.getD_some] at hl
    rw [hrightCache, Option.getD_some] at hr
    rw [hl, hr]
  have hempty : truncateHash output ∉ validDigests parameter cache leafIndex → shared = ∅ := by
    intro hnot
    rw [Set.eq_empty_iff_forall_notMem]
    intro entry hentry
    apply hnot
    exact ⟨entry, hentry.1, hentry.2.1⟩
  have hfreshPartnered : truncateHash output ∉ validDigests parameter cache leafIndex →
      fresh ∉ partneredEntries parameter cache' leafIndex := by
    intro hnot hmem
    rw [mem_partneredEntries] at hmem
    obtain ⟨found, hfound, hvalid, other, hother, otherOutput, hotherCache, hsame⟩ := hmem
    rw [hcache', cacheQuery_input_self (parameter := parameter) (leafIndex := leafIndex) fresh
      output cache, Option.some.injEq] at hfound
    rw [hcache', cacheQuery_input_other (parameter := parameter) (leafIndex := leafIndex) fresh
      output cache hother] at hotherCache
    apply hnot
    refine ⟨other, mem_validEntries.mpr ⟨otherOutput, hotherCache, ?_⟩, ?_⟩
    · rw [hsame]; exact hvalid
    · show truncateHash ((cache (input parameter leafIndex other)).getD 0) = truncateHash output
      rw [hotherCache, Option.getD_some, hsame, ← hfound]
  split_ifs with hhit
  · have h1 := Set.ncard_le_ncard hsub
    have h2 := Set.ncard_union_le old (insert fresh shared)
    have h3 := Set.ncard_insert_le fresh shared
    have : (partneredEntries parameter cache' leafIndex).ncard ≤ old.ncard + 2 := by omega
    exact_mod_cast this
  · have hsub' : partneredEntries parameter cache' leafIndex ⊆ old := by
      intro entry hentry
      have hmem := hsub hentry
      rw [hempty hhit] at hmem
      rcases hmem with hold | hins
      · exact hold
      · rw [Set.mem_insert_iff] at hins
        rcases hins with hfreshEq | hnone
        · subst hfreshEq
          exact absurd hentry (hfreshPartnered hhit)
        · exact absurd hnone (Set.notMem_empty _)
    simp only [add_zero]
    exact_mod_cast Set.ncard_le_ncard hsub'

end Fresh

end XmssSecurity.TargetSum.Direct.Collision
