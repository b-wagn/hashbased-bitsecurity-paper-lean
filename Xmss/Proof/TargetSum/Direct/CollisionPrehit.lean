import Xmss.Proof.TargetSum.Direct.CollisionSigning
import Xmss.Proof.Generic.Direct.EncodingPrehitExpected
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability
/-!
# Prehits with a colliding digest

A prehit (the signer accepts a randomizer whose encoding input the adversary had already
queried) only matters together with a collision: another cached encoding input of the epoch with
the same digest. This file bounds the probability of such a prehit with a collision by
`collisionRate q` per expected direct encoding query of an adversary making at most `q` of them.

The proof follows the adversary's run with a potential (`potential`): for each epoch not yet
signed, the epoch potential of `CollisionPotential`; for each signed epoch whose signer accepted
a cached randomizer without a partner, `(r + 1)/N` for the `r` remaining queries and the final
verification; and `1` once a prehit has a partner. A direct encoding query raises its
expectation by at most the rate, other queries and signing requests do not raise it.
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum.Direct.Collision

variable (q : ℕ) (secretKey : Generic.SecretKey)

/-- The entry's signer accepted a cached randomizer that has a partner in `cache`. -/
def EntryBad (cache : QueryCache HashSpec) (entry : SigningCacheEntry) : Prop :=
  entry.EncodingInputPrehit secretKey ∧ ∃ signature, entry.signature = some signature ∧
    IsPartnered secretKey.parameter cache entry.request.epoch
      (entry.request.message, signature.randomness)

/-- The entry's signer accepted a cached randomizer that has no partner in `cache`. -/
def EntryOpen (cache : QueryCache HashSpec) (entry : SigningCacheEntry) : Prop :=
  entry.EncodingInputPrehit secretKey ∧ ∀ signature, entry.signature = some signature →
    ¬ IsPartnered secretKey.parameter cache entry.request.epoch
      (entry.request.message, signature.randomness)

def StateBad (cache : QueryCache HashSpec) (trace : SigningCacheTrace) : Prop :=
  ∃ entry ∈ trace, EntryBad secretKey cache entry

noncomputable def openCount (cache : QueryCache HashSpec) (trace : SigningCacheTrace) : ℕ := by
  classical
  exact trace.countP fun entry => decide (EntryOpen secretKey cache entry)

/-- The potentials of the epochs not yet signed. -/
noncomputable def unsignedSum (cache : QueryCache HashSpec) (trace : SigningCacheTrace) : ℝ :=
  ∑ leafIndex : LeafIndex,
    if leafIndex ∈ trace.leafIndices then 0 else leafPotential q secretKey.parameter cache leafIndex

/-- The cached encoding inputs of the epochs not yet signed. -/
noncomputable def unsignedCount (cache : QueryCache HashSpec) (trace : SigningCacheTrace) : ℕ :=
  ∑ leafIndex : LeafIndex,
    if leafIndex ∈ trace.leafIndices then 0 else (entries secretKey.parameter cache leafIndex).ncard

/-- The potential of a state with `remaining` direct encoding queries left. -/
noncomputable def potential (cache : QueryCache HashSpec) (trace : SigningCacheTrace)
    (remaining : ℕ) : ℝ≥0∞ := by
  classical
  exact if trace.leafIndices.Nodup then
    if StateBad secretKey cache trace then 1
    else ENNReal.ofReal (unsignedSum q secretKey cache trace) +
      (openCount secretKey cache trace : ℝ≥0∞) * ENNReal.ofReal (((remaining : ℝ) + 1) / realN)
  else 0

/-- The invariant of the run: the cached encoding inputs of the epochs not yet signed and the
remaining queries number at most `q`, and every returned signature's input is cached with a
decodable digest. -/
structure Inv (cache : QueryCache HashSpec) (trace : SigningCacheTrace) (remaining : ℕ) :
    Prop where
  count : unsignedCount secretKey cache trace + remaining ≤ q
  valid : ∀ entry ∈ trace, ∀ signature, entry.signature = some signature →
    IsValid secretKey.parameter cache entry.request.epoch
      (entry.request.message, signature.randomness)

variable {q secretKey}

/-! ### Monotonicity and locality -/

theorem IsValid.mono {parameter : PublicParameter} {cache cache' : QueryCache HashSpec}
    (hle : cache ≤ cache') {leafIndex : LeafIndex} {entry : Message × Randomness}
    (h : IsValid parameter cache leafIndex entry) : IsValid parameter cache' leafIndex entry := by
  obtain ⟨output, hcache, hvalid⟩ := h
  exact ⟨output, hle hcache, hvalid⟩

theorem IsPartnered.mono {parameter : PublicParameter} {cache cache' : QueryCache HashSpec}
    (hle : cache ≤ cache') {leafIndex : LeafIndex} {entry : Message × Randomness}
    (h : IsPartnered parameter cache leafIndex entry) :
    IsPartnered parameter cache' leafIndex entry := by
  obtain ⟨output, hcache, hvalid, other, hother, otherOutput, hotherCache, hsame⟩ := h
  exact ⟨output, hle hcache, hvalid, other, hother, otherOutput, hle hotherCache, hsame⟩

theorem StateBad.mono {cache cache' : QueryCache HashSpec} (hle : cache ≤ cache')
    {trace trace' : SigningCacheTrace} (htrace : ∀ entry ∈ trace, entry ∈ trace')
    (h : StateBad secretKey cache trace) : StateBad secretKey cache' trace' := by
  obtain ⟨entry, hentry, hprehit, signature, hsignature, hpartnered⟩ := h
  exact ⟨entry, htrace entry hentry, hprehit, signature, hsignature, hpartnered.mono hle⟩

theorem isPartnered_congr {parameter : PublicParameter} {cache cache' : QueryCache HashSpec}
    {leafIndex : LeafIndex}
    (h : ∀ entry, cache' (input parameter leafIndex entry) = cache (input parameter leafIndex entry))
    (entry : Message × Randomness) :
    IsPartnered parameter cache' leafIndex entry ↔ IsPartnered parameter cache leafIndex entry := by
  simp only [IsPartnered, h]

theorem isValid_congr {parameter : PublicParameter} {cache cache' : QueryCache HashSpec}
    {leafIndex : LeafIndex}
    (h : ∀ entry, cache' (input parameter leafIndex entry) = cache (input parameter leafIndex entry))
    (entry : Message × Randomness) :
    IsValid parameter cache' leafIndex entry ↔ IsValid parameter cache leafIndex entry := by
  simp only [IsValid, h]

theorem entries_ncard_congr {parameter : PublicParameter} {cache cache' : QueryCache HashSpec}
    {leafIndex : LeafIndex}
    (h : ∀ entry, cache' (input parameter leafIndex entry) = cache (input parameter leafIndex entry)) :
    (entries parameter cache' leafIndex).ncard = (entries parameter cache leafIndex).ncard := by
  rw [(stats_congr h).1]

/-- The cached inputs of one unsigned epoch and the remaining queries number at most `q`. -/
theorem Inv.entries_add_le {cache : QueryCache HashSpec} {trace : SigningCacheTrace}
    {remaining : ℕ} (hinv : Inv q secretKey cache trace remaining) {leafIndex : LeafIndex}
    (hleaf : leafIndex ∉ trace.leafIndices) :
    (entries secretKey.parameter cache leafIndex).ncard + remaining ≤ q := by
  have hsingle : (entries secretKey.parameter cache leafIndex).ncard ≤
      unsignedCount secretKey cache trace := by
    have := Finset.single_le_sum (f := fun leafIndex : LeafIndex =>
      if leafIndex ∈ trace.leafIndices then 0 else
        (entries secretKey.parameter cache leafIndex).ncard)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ leafIndex)
    simpa [unsignedCount, hleaf] using this
  have := hinv.count
  omega

theorem potential_of_bad {cache : QueryCache HashSpec} {trace : SigningCacheTrace}
    {remaining : ℕ} (hnodup : trace.leafIndices.Nodup) (hbad : StateBad secretKey cache trace) :
    potential q secretKey cache trace remaining = 1 := by
  classical
  unfold potential
  rw [if_pos hnodup, if_pos hbad]

theorem potential_of_not_bad {cache : QueryCache HashSpec} {trace : SigningCacheTrace}
    {remaining : ℕ} (hnodup : trace.leafIndices.Nodup) (hbad : ¬ StateBad secretKey cache trace) :
    potential q secretKey cache trace remaining =
      ENNReal.ofReal (unsignedSum q secretKey cache trace) +
        (openCount secretKey cache trace : ℝ≥0∞) *
          ENNReal.ofReal (((remaining : ℝ) + 1) / realN) := by
  classical
  unfold potential
  rw [if_pos hnodup, if_neg hbad]

theorem potential_remaining_mono {cache : QueryCache HashSpec} {trace : SigningCacheTrace}
    {remaining remaining' : ℕ} (h : remaining ≤ remaining') :
    potential q secretKey cache trace remaining ≤ potential q secretKey cache trace remaining' := by
  classical
  unfold potential
  split_ifs
  · exact le_rfl
  · refine add_le_add le_rfl (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_))
    apply div_le_div_of_nonneg_right _ (by unfold realN; positivity)
    have : (remaining : ℝ) ≤ remaining' := by exact_mod_cast h
    linarith
  · exact le_rfl

/-! ### Expectations and congruence -/

theorem expect_le_of_support {β : Type} (computation : ProbComp β) (f : β → ℝ≥0∞) (bound : ℝ≥0∞)
    (h : ∀ x ∈ support computation, f x ≤ bound) :
    ∑' x, Pr[= x | computation] * f x ≤ bound := by
  calc
    _ ≤ ∑' x, Pr[= x | computation] * bound := by
      refine ENNReal.tsum_le_tsum fun x => ?_
      by_cases hx : x ∈ support computation
      · exact mul_le_mul' le_rfl (h x hx)
      · simp [probOutput_eq_zero_of_not_mem_support hx]
    _ ≤ bound := by
      rw [ENNReal.tsum_mul_right]
      exact (mul_le_mul' tsum_probOutput_le_one le_rfl).trans_eq (one_mul bound)

/-- Two caches that agree on every encoding input. -/
def AgreeOnEncoding (parameter : PublicParameter) (cache cache' : QueryCache HashSpec) : Prop :=
  ∀ leafIndex entry, cache' (input parameter leafIndex entry) = cache (input parameter leafIndex entry)

theorem stateBad_congr {cache cache' : QueryCache HashSpec}
    (h : AgreeOnEncoding secretKey.parameter cache cache') (trace : SigningCacheTrace) :
    StateBad secretKey cache' trace ↔ StateBad secretKey cache trace := by
  unfold StateBad EntryBad
  simp only [isPartnered_congr (h _)]

theorem openCount_congr {cache cache' : QueryCache HashSpec}
    (h : AgreeOnEncoding secretKey.parameter cache cache') (trace : SigningCacheTrace) :
    openCount secretKey cache' trace = openCount secretKey cache trace := by
  classical
  unfold openCount
  apply List.countP_congr
  intro entry _
  simp only [decide_eq_true_eq, EntryOpen, isPartnered_congr (h _)]

theorem potential_congr {cache cache' : QueryCache HashSpec}
    (h : AgreeOnEncoding secretKey.parameter cache cache') (trace : SigningCacheTrace)
    (remaining : ℕ) :
    potential q secretKey cache' trace remaining = potential q secretKey cache trace remaining := by
  classical
  have hsum : unsignedSum q secretKey cache' trace = unsignedSum q secretKey cache trace := by
    unfold unsignedSum
    exact Finset.sum_congr rfl fun leafIndex _ => by rw [leafPotential_congr (h leafIndex)]
  unfold potential
  rw [stateBad_congr h, openCount_congr h, hsum]

theorem Inv.congr {cache cache' : QueryCache HashSpec}
    (h : AgreeOnEncoding secretKey.parameter cache cache') {trace : SigningCacheTrace}
    {remaining : ℕ} (hinv : Inv q secretKey cache trace remaining) :
    Inv q secretKey cache' trace remaining := by
  refine ⟨?_, ?_⟩
  · have hcount : unsignedCount secretKey cache' trace = unsignedCount secretKey cache trace := by
      unfold unsignedCount
      exact Finset.sum_congr rfl fun leafIndex _ => by rw [entries_ncard_congr (h leafIndex)]
    rw [hcount]
    exact hinv.count
  · intro entry hentry signature hsignature
    exact (isValid_congr (h _) _).mpr (hinv.valid entry hentry signature hsignature)

theorem Inv.mono_remaining {cache : QueryCache HashSpec} {trace : SigningCacheTrace}
    {remaining remaining' : ℕ} (h : remaining' ≤ remaining)
    (hinv : Inv q secretKey cache trace remaining) : Inv q secretKey cache trace remaining' :=
  ⟨le_trans (Nat.add_le_add_left h _) hinv.count, hinv.valid⟩

/-! ### The traced implementation, query by query -/

theorem traced_hash_run (publicKey : PublicKey) (hashInput : HashInput)
    (cache : QueryCache HashSpec) (trace : SigningCacheTrace) :
    (cappedCacheTracedMappedAdversaryImpl publicKey secretKey (.inl (.inr hashInput))).run
        (cache, trace) =
      (fun result : Digest × QueryCache HashSpec => (result.1, (result.2, trace))) <$>
        (randomOracle (spec := HashSpec) hashInput).run cache := by
  rw [cappedCacheTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
    map_eq_bind_pure_comp]
  rfl

theorem traced_uniform_support (publicKey : PublicKey) (uniformInput : unifSpec.Domain)
    (cache : QueryCache HashSpec) (trace : SigningCacheTrace)
    (result : (OracleWorld + SigningSpec).Range (.inl (.inl uniformInput)) ×
      (QueryCache HashSpec × SigningCacheTrace))
    (hresult : result ∈ support
      ((cappedCacheTracedMappedAdversaryImpl publicKey secretKey (.inl (.inl uniformInput))).run
        (cache, trace))) :
    result.2 = (cache, trace) := by
  have htrace := cappedCacheTracedMappedAdversaryImpl_query_trace_update publicKey secretKey _
    cache trace result hresult
  have hcache := Direct.uniform_query_cache_eq publicKey secretKey uniformInput cache _
    (Direct.cappedCacheTracedMappedAdversaryImpl_query_base publicKey secretKey _ cache trace result
      hresult)
  rw [Prod.ext_iff]
  exact ⟨hcache, by simpa [signingCacheTraceUpdate] using htrace⟩

theorem traced_sign_run (publicKey : PublicKey) (request : SignRequest)
    (cache : QueryCache HashSpec) (trace : SigningCacheTrace) :
    (cappedCacheTracedMappedAdversaryImpl publicKey secretKey (.inr request)).run (cache, trace) =
      (fun result : Option Generic.Signature × QueryCache HashSpec =>
        (result.1, (result.2, trace ++ [SigningCacheEntry.mk request result.1 cache result.2]))) <$>
        (simulateQ romImpl (Signing.precomputedSignBoundedAttempts signingAttemptLimit secretKey
          request.epoch request.message)).run cache := by
  rw [cappedCacheTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
    map_eq_bind_pure_comp]
  change (simulateQ romImpl (Signing.precomputedCappedSign secretKey request.epoch
    request.message)).run cache >>= _ = _
  rw [Signing.precomputedCappedSign]
  rfl

theorem ne_input_of_not_encoding {parameter : PublicParameter} {hashInput : HashInput}
    (h : encodingInputLeafIndex? parameter hashInput = none) (leafIndex : LeafIndex)
    (entry : Message × Randomness) : input parameter leafIndex entry ≠ hashInput := by
  intro heq
  rw [← heq, encodingInputLeafIndex?_encodingInput] at h
  simp at h

/-! ### Steps that do not touch an encoding input -/

theorem step_uniform (publicKey : PublicKey) (uniformInput : unifSpec.Domain)
    (cache : QueryCache HashSpec) (trace : SigningCacheTrace) (remaining : ℕ)
    (hinv : Inv q secretKey cache trace remaining) :
    ∑' mid, Pr[= mid | (cappedCacheTracedMappedAdversaryImpl publicKey secretKey
        (.inl (.inl uniformInput))).run (cache, trace)] *
        potential q secretKey mid.2.1 mid.2.2 remaining ≤
      potential q secretKey cache trace remaining ∧
    ∀ mid ∈ support ((cappedCacheTracedMappedAdversaryImpl publicKey secretKey
        (.inl (.inl uniformInput))).run (cache, trace)),
      Inv q secretKey mid.2.1 mid.2.2 remaining := by
  refine ⟨expect_le_of_support _ _ _ fun mid hmid => ?_, fun mid hmid => ?_⟩
  · rw [traced_uniform_support publicKey uniformInput cache trace mid hmid]
  · rw [traced_uniform_support publicKey uniformInput cache trace mid hmid]
    exact hinv

theorem hash_support_cases (publicKey : PublicKey) (hashInput : HashInput)
    (cache : QueryCache HashSpec) (trace : SigningCacheTrace)
    (mid : Digest × (QueryCache HashSpec × SigningCacheTrace))
    (hmid : mid ∈ support ((cappedCacheTracedMappedAdversaryImpl publicKey secretKey
      (.inl (.inr hashInput))).run (cache, trace))) :
    mid.2.2 = trace ∧ (mid.2.1 = cache ∨ (cache hashInput = none ∧
      mid.2.1 = cache.cacheQuery hashInput mid.1)) := by
  rw [traced_hash_run, support_map] at hmid
  obtain ⟨⟨output, finalCache⟩, hbase, rfl⟩ := hmid
  refine ⟨rfl, ?_⟩
  cases hcached : cache hashInput with
  | some found =>
      rw [randomOracle, QueryImpl.withCaching_run_some _ hcached, support_pure,
        Set.mem_singleton_iff] at hbase
      exact Or.inl (congrArg Prod.snd hbase)
  | none =>
      rw [randomOracle_run_none_eq_uniformHashOutput _ _ hcached, support_map] at hbase
      obtain ⟨sampled, -, hsampled⟩ := hbase
      rw [← hsampled]
      exact Or.inr ⟨rfl, rfl⟩

theorem step_hash_other (publicKey : PublicKey) (hashInput : HashInput)
    (hother : encodingInputLeafIndex? secretKey.parameter hashInput = none)
    (cache : QueryCache HashSpec) (trace : SigningCacheTrace) (remaining : ℕ)
    (hinv : Inv q secretKey cache trace remaining) :
    ∑' mid, Pr[= mid | (cappedCacheTracedMappedAdversaryImpl publicKey secretKey
        (.inl (.inr hashInput))).run (cache, trace)] *
        potential q secretKey mid.2.1 mid.2.2 remaining ≤
      potential q secretKey cache trace remaining ∧
    ∀ mid ∈ support ((cappedCacheTracedMappedAdversaryImpl publicKey secretKey
        (.inl (.inr hashInput))).run (cache, trace)),
      Inv q secretKey mid.2.1 mid.2.2 remaining := by
  have hagree : ∀ mid ∈ support ((cappedCacheTracedMappedAdversaryImpl publicKey secretKey
      (.inl (.inr hashInput))).run (cache, trace)),
      mid.2.2 = trace ∧ AgreeOnEncoding secretKey.parameter cache mid.2.1 := by
    intro mid hmid
    obtain ⟨htrace, hcase⟩ := hash_support_cases publicKey hashInput cache trace mid hmid
    refine ⟨htrace, fun leafIndex entry => ?_⟩
    rcases hcase with heq | ⟨_, heq⟩
    · rw [heq]
    · rw [heq]
      exact QueryCache.cacheQuery_of_ne _ _ (ne_input_of_not_encoding hother leafIndex entry)
  refine ⟨expect_le_of_support _ _ _ fun mid hmid => ?_, fun mid hmid => ?_⟩
  · obtain ⟨htrace, hagreeMid⟩ := hagree mid hmid
    rw [htrace, potential_congr hagreeMid]
  · obtain ⟨htrace, hagreeMid⟩ := hagree mid hmid
    rw [htrace]
    exact hinv.congr hagreeMid

/-! ### A direct encoding query -/

theorem mem_leafIndices_of_mem {trace : SigningCacheTrace} {entry : SigningCacheEntry}
    (h : entry ∈ trace) : entry.request.epoch ∈ trace.leafIndices := by
  rw [SigningCacheTrace.leafIndices, List.mem_map]
  exact ⟨entry, h, rfl⟩

theorem agree_cacheQuery_other_leaf {parameter : PublicParameter} (cache : QueryCache HashSpec)
    {leafIndex leafIndex' : LeafIndex} (hne : leafIndex' ≠ leafIndex) (fresh : Message × Randomness)
    (output : Digest) (entry : Message × Randomness) :
    (cache.cacheQuery (input parameter leafIndex fresh) output) (input parameter leafIndex' entry) =
      cache (input parameter leafIndex' entry) :=
  QueryCache.cacheQuery_of_ne _ _ (input_ne_of_leafIndex_ne hne fresh entry)

/-- After a fresh query at an epoch, a cached decodable input of that epoch has a partner iff it
had one or the fresh digest equals its digest. -/
theorem isPartnered_cacheQuery_iff {parameter : PublicParameter} {cache : QueryCache HashSpec}
    {leafIndex : LeafIndex} {fresh : Message × Randomness}
    (hfresh : cache (input parameter leafIndex fresh) = none) (output : Digest)
    {entry : Message × Randomness} {found : Digest}
    (hfound : cache (input parameter leafIndex entry) = some found) :
    IsPartnered parameter (cache.cacheQuery (input parameter leafIndex fresh) output) leafIndex
        entry ↔
      IsPartnered parameter cache leafIndex entry ∨
        (Code.ValidDigest (found) ∧ output = found) := by
  have hne : entry ≠ fresh := by
    rintro rfl
    rw [hfresh] at hfound
    simp at hfound
  have hentry := cacheQuery_input_other (parameter := parameter) (leafIndex := leafIndex) fresh
    output cache hne
  constructor
  · rintro ⟨out, hout, hvalid, other, hother, otherOut, hotherCache, hsame⟩
    rw [hentry, hfound, Option.some.injEq] at hout
    subst hout
    by_cases hotherFresh : other = fresh
    · subst hotherFresh
      rw [cacheQuery_input_self, Option.some.injEq] at hotherCache
      subst hotherCache
      exact Or.inr ⟨hvalid, hsame⟩
    · rw [cacheQuery_input_other (parameter := parameter) (leafIndex := leafIndex) fresh output
        cache hotherFresh] at hotherCache
      exact Or.inl ⟨found, hfound, hvalid, other, hother, otherOut, hotherCache, hsame⟩
  · rintro (hpartnered | ⟨hvalid, hsame⟩)
    · exact hpartnered.mono (QueryCache.le_cacheQuery _ hfresh)
    · exact ⟨found, by rw [hentry, hfound], hvalid, fresh, fun h => hne h.symm, output,
        cacheQuery_input_self (parameter := parameter) (leafIndex := leafIndex) fresh output cache,
        hsame⟩

theorem unsignedSum_update {cache cache' : QueryCache HashSpec} {trace : SigningCacheTrace}
    {leafIndex : LeafIndex} (hleaf : leafIndex ∉ trace.leafIndices)
    (hother : ∀ leafIndex' ≠ leafIndex, ∀ entry,
      cache' (input secretKey.parameter leafIndex' entry) =
        cache (input secretKey.parameter leafIndex' entry)) :
    unsignedSum q secretKey cache' trace =
      (unsignedSum q secretKey cache trace - leafPotential q secretKey.parameter cache leafIndex) +
        leafPotential q secretKey.parameter cache' leafIndex := by
  unfold unsignedSum
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ leafIndex),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ leafIndex)]
  simp only [hleaf, if_false]
  have hrest : ∑ x ∈ Finset.univ.erase leafIndex,
      (if x ∈ trace.leafIndices then 0 else leafPotential q secretKey.parameter cache' x) =
      ∑ x ∈ Finset.univ.erase leafIndex,
        (if x ∈ trace.leafIndices then 0 else leafPotential q secretKey.parameter cache x) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [leafPotential_congr (hother x (Finset.ne_of_mem_erase hx))]
  rw [hrest]
  ring

theorem leafPotential_le_unsignedSum (hq : q + 1 ≤ 2 ^ 127) {cache : QueryCache HashSpec}
    {trace : SigningCacheTrace} {remaining : ℕ} (hinv : Inv q secretKey cache trace remaining)
    {leafIndex : LeafIndex} (hleaf : leafIndex ∉ trace.leafIndices) :
    leafPotential q secretKey.parameter cache leafIndex ≤ unsignedSum q secretKey cache trace := by
  unfold unsignedSum
  have := Finset.single_le_sum (f := fun x : LeafIndex =>
    if x ∈ trace.leafIndices then 0 else leafPotential q secretKey.parameter cache x)
    (fun x _ => by
      split_ifs with hx
      · exact le_rfl
      · apply leafPotential_nonneg hq
        have := hinv.entries_add_le hx
        omega) (Finset.mem_univ leafIndex)
  simpa [hleaf] using this

theorem unsignedCount_update {cache cache' : QueryCache HashSpec} {trace : SigningCacheTrace}
    {leafIndex : LeafIndex} (hleaf : leafIndex ∉ trace.leafIndices)
    (hother : ∀ leafIndex' ≠ leafIndex, ∀ entry,
      cache' (input secretKey.parameter leafIndex' entry) =
        cache (input secretKey.parameter leafIndex' entry))
    (hcount : (entries secretKey.parameter cache' leafIndex).ncard =
      (entries secretKey.parameter cache leafIndex).ncard + 1) :
    unsignedCount secretKey cache' trace = unsignedCount secretKey cache trace + 1 := by
  unfold unsignedCount
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ leafIndex),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ leafIndex)]
  simp only [hleaf, if_false, hcount]
  have hrest : ∑ x ∈ Finset.univ.erase leafIndex,
      (if x ∈ trace.leafIndices then 0 else (entries secretKey.parameter cache' x).ncard) =
      ∑ x ∈ Finset.univ.erase leafIndex,
        (if x ∈ trace.leafIndices then 0 else (entries secretKey.parameter cache x).ncard) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [entries_ncard_congr (hother x (Finset.ne_of_mem_erase hx))]
  rw [hrest]
  ring

theorem unsignedCount_signed {cache cache' : QueryCache HashSpec} {trace : SigningCacheTrace}
    {leafIndex : LeafIndex} (hleaf : leafIndex ∈ trace.leafIndices)
    (hother : ∀ leafIndex' ≠ leafIndex, ∀ entry,
      cache' (input secretKey.parameter leafIndex' entry) =
        cache (input secretKey.parameter leafIndex' entry)) :
    unsignedCount secretKey cache' trace = unsignedCount secretKey cache trace ∧
      unsignedSum q secretKey cache' trace = unsignedSum q secretKey cache trace := by
  constructor
  · unfold unsignedCount
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x = leafIndex
    · subst hx; simp [hleaf]
    · rw [entries_ncard_congr (hother x hx)]
  · unfold unsignedSum
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x = leafIndex
    · subst hx; simp [hleaf]
    · rw [leafPotential_congr (hother x hx)]

theorem stateBad_congr_trace {cache cache' : QueryCache HashSpec} {trace : SigningCacheTrace}
    (h : ∀ entry ∈ trace, ∀ x, cache' (input secretKey.parameter entry.request.epoch x) =
      cache (input secretKey.parameter entry.request.epoch x)) :
    StateBad secretKey cache' trace ↔ StateBad secretKey cache trace := by
  unfold StateBad
  constructor
  · rintro ⟨entry, hentry, hprehit, signature, hsignature, hpartnered⟩
    exact ⟨entry, hentry, hprehit, signature, hsignature,
      (isPartnered_congr (h entry hentry) _).mp hpartnered⟩
  · rintro ⟨entry, hentry, hprehit, signature, hsignature, hpartnered⟩
    exact ⟨entry, hentry, hprehit, signature, hsignature,
      (isPartnered_congr (h entry hentry) _).mpr hpartnered⟩

theorem openCount_congr_trace {cache cache' : QueryCache HashSpec} {trace : SigningCacheTrace}
    (h : ∀ entry ∈ trace, ∀ x, cache' (input secretKey.parameter entry.request.epoch x) =
      cache (input secretKey.parameter entry.request.epoch x)) :
    openCount secretKey cache' trace = openCount secretKey cache trace := by
  classical
  unfold openCount
  apply List.countP_congr
  intro entry hentry
  simp only [decide_eq_true_eq, EntryOpen, isPartnered_congr (h entry hentry)]

theorem ofReal_succ_weight (remaining : ℕ) :
    ENNReal.ofReal ((((remaining + 1 : ℕ) : ℝ) + 1) / realN) =
      ENNReal.ofReal (((remaining : ℝ) + 1) / realN) + ENNReal.ofReal (1 / realN) := by
  have hN : 0 < realN := by unfold realN; positivity
  rw [← ENNReal.ofReal_add (div_nonneg (by positivity) hN.le) (div_nonneg zero_le_one hN.le)]
  congr 1
  push_cast
  ring

/-- A fresh query at a signed epoch: unless its digest hits the digest of an open prehit, the
potential is unchanged; the hit has probability at most `open/N`. -/
theorem fresh_signed_le (_publicKey : PublicKey) {leafIndex : LeafIndex}
    {fresh : Message × Randomness} {cache : QueryCache HashSpec} {trace : SigningCacheTrace}
    {remaining : ℕ} (hinv : Inv q secretKey cache trace (remaining + 1))
    (hcached : cache (input secretKey.parameter leafIndex fresh) = none)
    (hleaf : leafIndex ∈ trace.leafIndices) (hnodup : trace.leafIndices.Nodup)
    (hbad : ¬ StateBad secretKey cache trace) :
    ∑' output : Digest, Pr[= output | $ᵗ Digest] *
        potential q secretKey (cache.cacheQuery (input secretKey.parameter leafIndex fresh) output)
          trace remaining ≤
      ENNReal.ofReal (unsignedSum q secretKey cache trace) +
        (openCount secretKey cache trace : ℝ≥0∞) *
          ENNReal.ofReal (((remaining : ℝ) + 1) / realN) +
        (openCount secretKey cache trace : ℝ≥0∞) * ENNReal.ofReal (1 / realN) := by
  classical
  set parameter := secretKey.parameter
  set hashInput := input parameter leafIndex fresh
  have hN : 0 < realN := by unfold realN; positivity
  set X := ENNReal.ofReal (unsignedSum q secretKey cache trace) +
    (openCount secretKey cache trace : ℝ≥0∞) * ENNReal.ofReal (((remaining : ℝ) + 1) / realN)
  set hitSet : Set Digest := {digest | ∃ entry ∈ trace, entry.request.epoch = leafIndex ∧
    EntryOpen secretKey cache entry ∧ ∃ signature found, entry.signature = some signature ∧
      cache (input parameter leafIndex (entry.request.message, signature.randomness)) =
        some found ∧ digest = found}
  have hother : ∀ output : Digest, ∀ leafIndex' ≠ leafIndex, ∀ entry,
      (cache.cacheQuery hashInput output) (input parameter leafIndex' entry) =
        cache (input parameter leafIndex' entry) :=
    fun output leafIndex' hne entry => agree_cacheQuery_other_leaf cache hne fresh output entry
  -- partner status of prehits is unchanged without a hit
  have hiff : ∀ output : Digest, output ∉ hitSet → ∀ entry ∈ trace,
      entry.EncodingInputPrehit secretKey → ∀ signature, entry.signature = some signature →
        (IsPartnered parameter (cache.cacheQuery hashInput output) entry.request.epoch
          (entry.request.message, signature.randomness) ↔
          IsPartnered parameter cache entry.request.epoch
            (entry.request.message, signature.randomness)) := by
    intro output hhit entry hentry hprehit signature hsignature
    refine ⟨fun hnew => ?_, fun hold => hold.mono (QueryCache.le_cacheQuery _ hcached)⟩
    by_contra hold
    by_cases hepoch : entry.request.epoch = leafIndex
    · obtain ⟨found, hfound, _⟩ := hinv.valid entry hentry signature hsignature
      rw [hepoch] at hfound hnew hold
      rcases (isPartnered_cacheQuery_iff hcached output hfound).mp hnew with h | ⟨_, hsame⟩
      · exact hold h
      · apply hhit
        refine ⟨entry, hentry, hepoch, ⟨hprehit, fun other hother' => ?_⟩, signature, found,
          hsignature, hfound, hsame⟩
        rw [hsignature, Option.some.injEq] at hother'
        subst hother'
        rw [hepoch]
        exact hold
    · exact hold ((isPartnered_congr (hother output _ hepoch) _).mp hnew)
  have hafter : ∀ output : Digest,
      potential q secretKey (cache.cacheQuery hashInput output) trace remaining ≤
        if output ∈ hitSet then 1 else X := by
    intro output
    split_ifs with hhit
    · obtain ⟨entry, hentry, hepoch, hopen, signature, found, hsignature, hfound, hdigest⟩ := hhit
      have hpartnered : IsPartnered parameter (cache.cacheQuery hashInput output)
          entry.request.epoch (entry.request.message, signature.randomness) := by
        rw [hepoch]
        refine (isPartnered_cacheQuery_iff hcached output hfound).mpr (Or.inr ⟨?_, hdigest⟩)
        obtain ⟨out, hout, hvalid⟩ := hinv.valid entry hentry signature hsignature
        rw [hepoch, hfound, Option.some.injEq] at hout
        rw [hout]
        exact hvalid
      have hbad' : StateBad secretKey (cache.cacheQuery hashInput output) trace :=
        ⟨entry, hentry, hopen.1, signature, hsignature, hpartnered⟩
      simp [potential, hnodup, hbad']
    · have hbad' : ¬ StateBad secretKey (cache.cacheQuery hashInput output) trace := by
        rintro ⟨entry, hentry, hprehit, signature, hsignature, hpartnered⟩
        exact hbad ⟨entry, hentry, hprehit, signature, hsignature,
          (hiff output hhit entry hentry hprehit signature hsignature).mp hpartnered⟩
      have hopen : openCount secretKey (cache.cacheQuery hashInput output) trace =
          openCount secretKey cache trace := by
        unfold openCount
        apply List.countP_congr
        intro entry hentry
        simp only [decide_eq_true_eq, EntryOpen]
        constructor
        · rintro ⟨hprehit, hnot⟩
          exact ⟨hprehit, fun signature hsignature hold =>
            hnot signature hsignature ((hiff output hhit entry hentry hprehit signature
              hsignature).mpr hold)⟩
        · rintro ⟨hprehit, hnot⟩
          exact ⟨hprehit, fun signature hsignature hnew =>
            hnot signature hsignature ((hiff output hhit entry hentry hprehit signature
              hsignature).mp hnew)⟩
      have hsum := (unsignedCount_signed (q := q) hleaf (hother output)).2
      simp only [potential, hnodup, hbad', if_true, if_false, hopen, hsum, X, le_refl]
  -- the hit set has at most one digest, and only if some prehit is open
  have hhitCard : (hitSet.ncard : ℝ≥0∞) ≤ (openCount secretKey cache trace : ℝ≥0∞) := by
    have hle1 : hitSet.ncard ≤ 1 := by
      rw [Set.ncard_le_one]
      rintro a ⟨e1, he1, hep1, _, s1, f1, hs1, hf1, rfl⟩ b ⟨e2, he2, hep2, _, s2, f2, hs2, hf2, rfl⟩
      have heq : e1 = e2 := List.inj_on_of_nodup_map
        (by simpa [SigningCacheTrace.leafIndices] using hnodup) he1 he2 (hep1.trans hep2.symm)
      subst heq
      rw [hs1, Option.some.injEq] at hs2
      subst hs2
      rw [hf1, Option.some.injEq] at hf2
      rw [hf2]
    by_cases hempty : hitSet = ∅
    · rw [hempty, Set.ncard_empty]
      simp
    · obtain ⟨digest, hdigest⟩ := Set.nonempty_iff_ne_empty.mpr hempty
      obtain ⟨entry, hentry, _, hopen, _⟩ := hdigest
      have hpos : 0 < openCount secretKey cache trace := by
        unfold openCount
        exact List.countP_pos_iff.mpr ⟨entry, hentry, by simpa using hopen⟩
      exact_mod_cast hle1.trans hpos
  calc
    _ ≤ ∑' output : Digest, Pr[= output | $ᵗ Digest] *
          (if output ∈ hitSet then 1 else X) :=
      ENNReal.tsum_le_tsum fun output => mul_le_mul' le_rfl (hafter output)
    _ = Pr[fun output : Digest => output ∈ hitSet | $ᵗ Digest] * 1 +
          Pr[fun output : Digest => ¬ output ∈ hitSet | $ᵗ Digest] * X :=
      tsum_uniform_ite _ 1 X
    _ ≤ (hitSet.ncard : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) + X := by
      rw [probEvent_uniform_mem, mul_one]
      exact add_le_add le_rfl ((mul_le_mul' probEvent_le_one le_rfl).trans_eq (one_mul X))
    _ ≤ (openCount secretKey cache trace : ℝ≥0∞) * ENNReal.ofReal (1 / realN) + X := by
      apply add_le_add _ le_rfl
      have h1N : ENNReal.ofReal (1 / realN) = 1 / ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
        rw [ENNReal.ofReal_div_of_pos hN, ENNReal.ofReal_one]
        simp [realN, digestBits]
        norm_num
      rw [h1N, ← mul_div_assoc, mul_one]
      exact ENNReal.div_le_div_right hhitCard _
    _ = _ := by rw [add_comm]

/-- A fresh query at an epoch not yet signed raises the expected potential by at most the
rate. -/
theorem fresh_unsigned_le (hq : q + 1 ≤ 2 ^ 127) {leafIndex : LeafIndex}
    {fresh : Message × Randomness} {cache : QueryCache HashSpec} {trace : SigningCacheTrace}
    {remaining : ℕ} (hinv : Inv q secretKey cache trace (remaining + 1))
    (hcached : cache (input secretKey.parameter leafIndex fresh) = none)
    (hleaf : leafIndex ∉ trace.leafIndices) (hnodup : trace.leafIndices.Nodup)
    (hbad : ¬ StateBad secretKey cache trace) :
    ∑' output : Digest, Pr[= output | $ᵗ Digest] *
        potential q secretKey (cache.cacheQuery (input secretKey.parameter leafIndex fresh) output)
          trace remaining ≤
      ENNReal.ofReal (unsignedSum q secretKey cache trace) +
        (openCount secretKey cache trace : ℝ≥0∞) *
          ENNReal.ofReal (((remaining : ℝ) + 1) / realN) + collisionRate q := by
  classical
  set hashInput := input secretKey.parameter leafIndex fresh
  set φ := leafPotential q secretKey.parameter cache leafIndex
  set U := unsignedSum q secretKey cache trace
  set openW := (openCount secretKey cache trace : ℝ≥0∞) *
    ENNReal.ofReal (((remaining : ℝ) + 1) / realN)
  have hother : ∀ output : Digest, ∀ leafIndex' ≠ leafIndex, ∀ entry,
      (cache.cacheQuery hashInput output) (input secretKey.parameter leafIndex' entry) =
        cache (input secretKey.parameter leafIndex' entry) :=
    fun output leafIndex' hne entry => agree_cacheQuery_other_leaf cache hne fresh output entry
  have htrace : ∀ output : Digest, ∀ entry ∈ trace, ∀ x,
      (cache.cacheQuery hashInput output) (input secretKey.parameter entry.request.epoch x) =
        cache (input secretKey.parameter entry.request.epoch x) := by
    intro output entry hentry x
    refine hother output _ ?_ x
    rintro hepoch
    exact hleaf (hepoch ▸ mem_leafIndices_of_mem hentry)
  have hφU : φ ≤ U := leafPotential_le_unsignedSum hq hinv hleaf
  have hφ0 : 0 ≤ φ := by
    apply leafPotential_nonneg hq
    have := hinv.entries_add_le hleaf
    omega
  have hafter : ∀ output : Digest,
      potential q secretKey (cache.cacheQuery hashInput output) trace remaining ≤
        ENNReal.ofReal (U - φ) +
          ENNReal.ofReal (leafPotential q secretKey.parameter (cache.cacheQuery hashInput output) leafIndex) +
          openW := by
    intro output
    have hbad' : ¬ StateBad secretKey (cache.cacheQuery hashInput output) trace := by
      rw [stateBad_congr_trace (htrace output)]
      exact hbad
    simp only [potential, hnodup, hbad', if_true, if_false,
      openCount_congr_trace (htrace output), unsignedSum_update hleaf (hother output)]
    exact add_le_add ENNReal.ofReal_add_le le_rfl
  have hK : (entries secretKey.parameter cache leafIndex).ncard + 1 ≤ q + 1 := by
    have := hinv.entries_add_le hleaf
    omega
  calc
    _ ≤ ∑' output : Digest, Pr[= output | $ᵗ Digest] *
          (ENNReal.ofReal (U - φ) +
            ENNReal.ofReal (leafPotential q secretKey.parameter (cache.cacheQuery hashInput output) leafIndex) +
            openW) :=
      ENNReal.tsum_le_tsum fun output => mul_le_mul' le_rfl (hafter output)
    _ = ENNReal.ofReal (U - φ) + (∑' output : Digest, Pr[= output | $ᵗ Digest] *
          ENNReal.ofReal (leafPotential q secretKey.parameter (cache.cacheQuery hashInput output) leafIndex)) +
          openW := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add, ENNReal.tsum_add, tsum_uniform_const, tsum_uniform_const]
    _ ≤ ENNReal.ofReal (U - φ) + (ENNReal.ofReal φ + collisionRate q) + openW := by
      gcongr
      exact expected_leafPotential_cacheQuery_le hq cache leafIndex fresh hcached hK
    _ = ENNReal.ofReal U + openW + collisionRate q := by
      rw [← add_assoc, ← ENNReal.ofReal_add (by linarith) hφ0, sub_add_cancel]
      ring

/-- A direct encoding query: the potential, with one query fewer left, rises by at most the
rate in expectation. -/
theorem step_hash_encoding (hq : q + 1 ≤ 2 ^ 127) (publicKey : PublicKey) (leafIndex : LeafIndex)
    (fresh : Message × Randomness) (cache : QueryCache HashSpec) (trace : SigningCacheTrace)
    (remaining : ℕ) (hinv : Inv q secretKey cache trace (remaining + 1)) :
    ∑' mid, Pr[= mid | (cappedCacheTracedMappedAdversaryImpl publicKey secretKey
        (.inl (.inr (input secretKey.parameter leafIndex fresh)))).run (cache, trace)] *
        potential q secretKey mid.2.1 mid.2.2 remaining ≤
      potential q secretKey cache trace (remaining + 1) + collisionRate q ∧
    ∀ mid ∈ support ((cappedCacheTracedMappedAdversaryImpl publicKey secretKey
        (.inl (.inr (input secretKey.parameter leafIndex fresh)))).run (cache, trace)),
      Inv q secretKey mid.2.1 mid.2.2 remaining := by
  classical
  set parameter := secretKey.parameter
  set hashInput := input parameter leafIndex fresh
  cases hcached : cache hashInput with
  | some found =>
      have hrun : (cappedCacheTracedMappedAdversaryImpl publicKey secretKey
          (.inl (.inr hashInput))).run (cache, trace) = pure (found, (cache, trace)) := by
        rw [traced_hash_run, randomOracle, QueryImpl.withCaching_run_some _ hcached]
        simp
      rw [hrun, tsum_probOutput_pure_mul]
      refine ⟨(potential_remaining_mono (Nat.le_succ _)).trans le_self_add, ?_⟩
      intro mid hmid
      rw [support_pure, Set.mem_singleton_iff] at hmid
      subst hmid
      exact hinv.mono_remaining (Nat.le_succ _)
  | none =>
      have hrun : (cappedCacheTracedMappedAdversaryImpl publicKey secretKey
          (.inl (.inr hashInput))).run (cache, trace) =
          (fun output : Digest => (output, (cache.cacheQuery hashInput output, trace))) <$>
            ($ᵗ Digest) := by
        rw [traced_hash_run, randomOracle_run_none_eq_uniformHashOutput _ _ hcached]
        simp [uniformHashOutput, Functor.map_map]
      have hle : ∀ output : Digest, cache ≤ cache.cacheQuery hashInput output :=
        fun output => QueryCache.le_cacheQuery _ hcached
      have hother : ∀ output : Digest, ∀ leafIndex' ≠ leafIndex, ∀ entry,
          (cache.cacheQuery hashInput output) (input parameter leafIndex' entry) =
            cache (input parameter leafIndex' entry) :=
        fun output leafIndex' hne entry => agree_cacheQuery_other_leaf cache hne fresh output entry
      have hcount := hinv.count
      rw [hrun, tsum_probOutput_map_mul]
      constructor
      swap
      · intro mid hmid
        rw [support_map] at hmid
        obtain ⟨output, -, rfl⟩ := hmid
        refine ⟨?_, fun entry hentry signature hsignature =>
          (hinv.valid entry hentry signature hsignature).mono (hle output)⟩
        by_cases hleaf : leafIndex ∈ trace.leafIndices
        · rw [(unsignedCount_signed (q := q) hleaf (hother output)).1]
          omega
        · rw [unsignedCount_update hleaf (hother output)
            (ncard_entries_cacheQuery fresh output hcached)]
          omega
      by_cases hnodup : trace.leafIndices.Nodup
      swap
      · refine le_trans (le_of_eq ?_) bot_le
        simp [potential, hnodup]
      by_cases hbad : StateBad secretKey cache trace
      · have hbadAfter : ∀ output : Digest,
            potential q secretKey (cache.cacheQuery hashInput output) trace remaining = 1 := by
          intro output
          simp [potential, hnodup, hbad.mono (hle output) (fun _ h => h)]
        simp_rw [hbadAfter]
        rw [tsum_uniform_const]
        simp [potential, hnodup, hbad]
      have hbefore : potential q secretKey cache trace (remaining + 1) =
          ENNReal.ofReal (unsignedSum q secretKey cache trace) +
            (openCount secretKey cache trace : ℝ≥0∞) *
              ENNReal.ofReal (((remaining : ℝ) + 1) / realN) +
            (openCount secretKey cache trace : ℝ≥0∞) * ENNReal.ofReal (1 / realN) := by
        simp only [potential, hnodup, hbad, if_true, if_false]
        rw [ofReal_succ_weight, mul_add, add_assoc]
      rw [hbefore]
      by_cases hleaf : leafIndex ∈ trace.leafIndices
      · exact (fresh_signed_le publicKey hinv hcached hleaf hnodup hbad).trans le_self_add
      · refine (fresh_unsigned_le hq hinv hcached hleaf hnodup hbad).trans ?_
        exact add_le_add (le_self_add) le_rfl

/-! ### A signing request -/

/-- The facts about one signing request used below. -/
theorem sign_facts (request : SignRequest) (cache : QueryCache HashSpec)
    (result : Option Generic.Signature × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ romImpl (Signing.precomputedSignBoundedAttempts
      signingAttemptLimit secretKey request.epoch request.message)).run cache)) :
    cache ≤ result.2 ∧
    (∀ leafIndex ≠ request.epoch, ∀ entry,
      result.2 (input secretKey.parameter leafIndex entry) =
        cache (input secretKey.parameter leafIndex entry)) ∧
    (∀ signature, result.1 = some signature →
      IsValid secretKey.parameter result.2 request.epoch
        (request.message, signature.randomness)) ∧
    (∀ entry, cache (input secretKey.parameter request.epoch entry) = none →
      IsValid secretKey.parameter result.2 request.epoch entry →
        ∃ signature, result.1 = some signature ∧
          entry = (request.message, signature.randomness)) := by
  obtain ⟨hle, hvalid, hnew⟩ := precomputedSignBoundedAttempts_newValid secretKey request.epoch
    request.message signingAttemptLimit cache result hresult
  refine ⟨hle, ?_, hvalid, hnew⟩
  intro leafIndex hne entry
  have hcapped : (result.1, result.2) ∈ support ((simulateQ romImpl
      (Signing.precomputedCappedSign secretKey request.epoch request.message)).run cache) := by
    rw [Signing.precomputedCappedSign]
    exact hresult
  cases hcache : cache (input secretKey.parameter leafIndex entry) with
  | none =>
      exact Signing.precomputedCappedSign_preserves_other_leafIndex_encodingInput secretKey
        request.epoch leafIndex request.message entry cache result.2 result.1 hcapped
        (fun h => hne h.symm) hcache
  | some found => exact hle hcache

theorem step_sign (hq : q + 1 ≤ 2 ^ 127) (publicKey : PublicKey) (request : SignRequest)
    (cache : QueryCache HashSpec) (trace : SigningCacheTrace) (remaining : ℕ)
    (hinv : Inv q secretKey cache trace remaining) :
    ∑' mid, Pr[= mid | (cappedCacheTracedMappedAdversaryImpl publicKey secretKey
        (.inr request)).run (cache, trace)] *
        potential q secretKey mid.2.1 mid.2.2 remaining ≤
      potential q secretKey cache trace remaining ∧
    ∀ mid ∈ support ((cappedCacheTracedMappedAdversaryImpl publicKey secretKey
        (.inr request)).run (cache, trace)),
      Inv q secretKey mid.2.1 mid.2.2 remaining := by
  classical
  set leafIndex := request.epoch
  set message := request.message
  set base := (simulateQ romImpl (Signing.precomputedSignBoundedAttempts signingAttemptLimit
    secretKey leafIndex message)).run cache
  set newTrace := fun result : Option Generic.Signature × QueryCache HashSpec =>
    trace ++ [SigningCacheEntry.mk request result.1 cache result.2]
  have hleafIndices : ∀ result : Option Generic.Signature × QueryCache HashSpec,
      (newTrace result).leafIndices = trace.leafIndices ++ [leafIndex] := by
    intro result
    simp [newTrace, SigningCacheTrace.leafIndices, leafIndex]
  rw [traced_sign_run, tsum_probOutput_map_mul]
  constructor
  swap
  · -- the invariant
    intro mid hmid
    rw [support_map] at hmid
    obtain ⟨result, hresult, rfl⟩ := hmid
    obtain ⟨hle, hother, hvalid, -⟩ := sign_facts request cache result hresult
    refine ⟨?_, ?_⟩
    · refine le_trans (Nat.add_le_add_right ?_ remaining) hinv.count
      unfold unsignedCount
      refine Finset.sum_le_sum fun leafIndex' _ => ?_
      have hmem : leafIndex' ∈ (newTrace result).leafIndices ↔
          leafIndex' ∈ trace.leafIndices ∨ leafIndex' = leafIndex := by
        rw [hleafIndices, List.mem_append, List.mem_singleton]
      change (if leafIndex' ∈ (newTrace result).leafIndices then 0 else
        (entries secretKey.parameter result.2 leafIndex').ncard) ≤ _
      split_ifs with h1 h2 h2
      · exact le_rfl
      · exact Nat.zero_le _
      · exact absurd (hmem.mpr (Or.inl h2)) h1
      · have hne : leafIndex' ≠ leafIndex := fun h => h1 (hmem.mpr (Or.inr h))
        rw [entries_ncard_congr (hother leafIndex' hne)]
    · intro entry hentry signature hsignature
      rcases List.mem_append.mp hentry with hold | hnew
      · exact (hinv.valid entry hold signature hsignature).mono hle
      · rw [List.mem_singleton] at hnew
        subst hnew
        exact hvalid signature hsignature
  -- the potential
  have hzeroOf : ∀ result : Option Generic.Signature × QueryCache HashSpec,
      ¬ (newTrace result).leafIndices.Nodup →
        potential q secretKey result.2 (newTrace result) remaining = 0 := by
    intro result hnot
    simp [potential, hnot]
  by_cases hnodup : trace.leafIndices.Nodup
  swap
  · refine le_trans (le_of_eq ?_) bot_le
    refine ENNReal.tsum_eq_zero.mpr fun result => ?_
    rw [hzeroOf result (fun h => hnodup (by
      rw [hleafIndices] at h
      exact h.sublist (List.sublist_append_left _ _))), mul_zero]
  by_cases hsigned : leafIndex ∈ trace.leafIndices
  · refine le_trans (le_of_eq ?_) bot_le
    refine ENNReal.tsum_eq_zero.mpr fun result => ?_
    rw [hzeroOf result (fun h => by
      rw [hleafIndices, List.nodup_append] at h
      exact h.2.2 _ hsigned _ (List.mem_singleton_self _) rfl), mul_zero]
  have hnodup' : ∀ result : Option Generic.Signature × QueryCache HashSpec,
      (newTrace result).leafIndices.Nodup := by
    intro result
    rw [hleafIndices, List.nodup_append]
    refine ⟨hnodup, List.nodup_singleton _, ?_⟩
    intro a ha b hb hab
    rw [List.mem_singleton] at hb
    subst hb hab
    exact hsigned ha
  by_cases hbad : StateBad secretKey cache trace
  · refine expect_le_of_support _ _ _ fun result hresult => ?_
    obtain ⟨hle, -, -, -⟩ := sign_facts request cache result hresult
    have hbad' : StateBad secretKey result.2 (newTrace result) :=
      hbad.mono hle fun entry hentry => List.mem_append_left _ hentry
    rw [potential_of_bad (hnodup' result) hbad', potential_of_bad hnodup hbad]
  -- the race
  set S := partneredRandomizers secretKey.parameter cache leafIndex message
  set W := validRandomizers secretKey.parameter cache leafIndex message
  set weight := ENNReal.ofReal (((remaining : ℝ) + 1) / realN)
  set φ := leafPotential q secretKey.parameter cache leafIndex
  set U := unsignedSum q secretKey cache trace
  set open₀ := (openCount secretKey cache trace : ℝ≥0∞)
  have hSW : S ⊆ W := partneredRandomizers_subset cache leafIndex message
  have hW : ∀ randomness ∈ W, DecodableAt secretKey.parameter leafIndex message cache randomness := by
    intro randomness hrandomness
    simpa [W, validRandomizers] using hrandomness
  have hφU : φ ≤ U := leafPotential_le_unsignedSum hq hinv hsigned
  have hφ0 : 0 ≤ φ := by
    apply leafPotential_nonneg hq
    have := hinv.entries_add_le hsigned
    omega
  have hafter : ∀ result ∈ support base,
      potential q secretKey result.2 (newTrace result) remaining ≤
        raceCost S W weight result.1 + (ENNReal.ofReal (U - φ) + open₀ * weight) := by
    intro result hresult
    obtain ⟨hle, hother, hvalid, hnew⟩ := sign_facts request cache result hresult
    have holdLeaf : ∀ entry ∈ trace, entry.request.epoch ≠ leafIndex := by
      intro entry hentry heq
      exact hsigned (heq ▸ mem_leafIndices_of_mem hentry)
    have hagreeOld : ∀ entry ∈ trace, ∀ x,
        result.2 (input secretKey.parameter entry.request.epoch x) =
          cache (input secretKey.parameter entry.request.epoch x) :=
      fun entry hentry x => hother _ (holdLeaf entry hentry) x
    set newEntry := SigningCacheEntry.mk request result.1 cache result.2
    have hsum : unsignedSum q secretKey result.2 (newTrace result) = U - φ := by
      have hsplit : U = φ + ∑ x ∈ Finset.univ.erase leafIndex,
          (if x ∈ trace.leafIndices then 0 else leafPotential q secretKey.parameter cache x) := by
        simp only [U, unsignedSum]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ leafIndex)]
        simp [hsigned, φ]
      rw [hsplit, add_sub_cancel_left]
      unfold unsignedSum
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ leafIndex)]
      simp only [hleafIndices, List.mem_append, List.mem_singleton, or_true, if_true, zero_add]
      refine Finset.sum_congr rfl fun x hx => ?_
      have hne := Finset.ne_of_mem_erase hx
      simp only [hne, or_false]
      rw [leafPotential_congr (hother x hne)]
    have hbadOld : ¬ ∃ entry ∈ trace, EntryBad secretKey result.2 entry := by
      rintro ⟨entry, hentry, hprehit, signature, hsignature, hpartnered⟩
      exact hbad ⟨entry, hentry, hprehit, signature, hsignature,
        (isPartnered_congr (hagreeOld entry hentry) _).mp hpartnered⟩
    have hopenOld : trace.countP (fun entry => decide (EntryOpen secretKey result.2 entry)) =
        openCount secretKey cache trace := by
      unfold openCount
      apply List.countP_congr
      intro entry hentry
      simp only [decide_eq_true_eq, EntryOpen, isPartnered_congr (hagreeOld entry hentry)]
    have hpartnerOld : ∀ signature, result.1 = some signature →
        cache (input secretKey.parameter leafIndex (message, signature.randomness)) ≠ none →
        IsPartnered secretKey.parameter result.2 leafIndex (message, signature.randomness) →
          IsPartnered secretKey.parameter cache leafIndex (message, signature.randomness) := by
      intro signature hsignature hcached hpartnered
      obtain ⟨out, hout, hvalidOut, other, hotherNe, otherOut, hotherCache, hsame⟩ := hpartnered
      obtain ⟨found, hfound⟩ := Option.ne_none_iff_exists'.mp hcached
      have hfoundOut : found = out := by
        have := hle hfound
        rw [hout, Option.some.injEq] at this
        exact this.symm
      subst hfoundOut
      refine ⟨found, hfound, hvalidOut, other, hotherNe, otherOut, ?_, hsame⟩
      cases hotherOld : cache (input secretKey.parameter leafIndex other) with
      | some otherFound =>
          have := hle hotherOld
          rw [hotherCache, Option.some.injEq] at this
          rw [this]
      | none =>
          exfalso
          obtain ⟨signature', hsignature', hotherEq⟩ := hnew other hotherOld
            ⟨otherOut, hotherCache, by rw [hsame]; exact hvalidOut⟩
          rw [hsignature, Option.some.injEq] at hsignature'
          subst hsignature'
          exact hotherNe hotherEq
    by_cases hnewBad : EntryBad secretKey result.2 newEntry
    · obtain ⟨⟨signature, found, hsignature, hfound⟩, signature', hsignature', hpartnered⟩ :=
        hnewBad
      change result.1 = some signature at hsignature
      change result.1 = some signature' at hsignature'
      rw [hsignature, Option.some.injEq] at hsignature'
      subst hsignature'
      have hfound' : cache (input secretKey.parameter leafIndex (message, signature.randomness)) =
          some found := hfound
      have hS : signature.randomness ∈ S := by
        simp only [S, mem_partneredRandomizers]
        exact hpartnerOld signature hsignature (by rw [hfound']; exact Option.some_ne_none _)
          hpartnered
      have hcost : raceCost S W weight result.1 = 1 := by
        rw [hsignature]
        simp [raceCost, hS]
      rw [hcost]
      have hbad' : StateBad secretKey result.2 (newTrace result) :=
        ⟨newEntry, List.mem_append_right _ (List.mem_singleton_self _),
          ⟨signature, found, hsignature, hfound⟩, signature, hsignature, hpartnered⟩
      exact (le_of_eq (potential_of_bad (hnodup' result) hbad')).trans le_self_add
    · have hbad' : ¬ StateBad secretKey result.2 (newTrace result) := by
        rintro ⟨entry, hentry, hentryBad⟩
        rcases List.mem_append.mp hentry with hold | hthis
        · exact hbadOld ⟨entry, hold, hentryBad⟩
        · rw [List.mem_singleton] at hthis
          subst hthis
          exact hnewBad hentryBad
      have hcountNat : openCount secretKey result.2 (newTrace result) =
          openCount secretKey cache trace +
            if EntryOpen secretKey result.2 newEntry then 1 else 0 := by
        have happend : openCount secretKey result.2 (newTrace result) =
            trace.countP (fun entry => decide (EntryOpen secretKey result.2 entry)) +
              [newEntry].countP (fun entry => decide (EntryOpen secretKey result.2 entry)) := by
          unfold openCount
          exact List.countP_append
        rw [happend, hopenOld, List.countP_singleton]
        by_cases hopen : EntryOpen secretKey result.2 newEntry <;> simp [hopen]
      have hcount : (openCount secretKey result.2 (newTrace result) : ℝ≥0∞) =
          open₀ + if EntryOpen secretKey result.2 newEntry then 1 else 0 := by
        rw [hcountNat]
        by_cases hopen : EntryOpen secretKey result.2 newEntry <;> simp [hopen, open₀]
      have hpotential : potential q secretKey result.2 (newTrace result) remaining =
          ENNReal.ofReal (U - φ) +
            (open₀ + if EntryOpen secretKey result.2 newEntry then 1 else 0) * weight := by
        rw [potential_of_not_bad (hnodup' result) hbad', hsum, hcount]
      rw [hpotential]
      by_cases hopen : EntryOpen secretKey result.2 newEntry
      · obtain ⟨⟨signature, found, hsignature, hfound⟩, hnotPartnered⟩ := hopen
        change result.1 = some signature at hsignature
        have hfound' : cache (input secretKey.parameter leafIndex
            (message, signature.randomness)) = some found := hfound
        have hWmem : signature.randomness ∈ W := by
          obtain ⟨out, hout, hvalidOut⟩ := hvalid signature hsignature
          have := hle hfound'
          rw [hout, Option.some.injEq] at this
          subst this
          simp only [W, validRandomizers, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨out, hfound', hvalidOut⟩
        have hSmem : signature.randomness ∉ S := by
          simp only [S, mem_partneredRandomizers]
          intro hold
          exact hnotPartnered signature hsignature (hold.mono hle)
        have hcost : raceCost S W weight result.1 = weight := by
          rw [hsignature]
          simp [raceCost, hSmem, hWmem]
        rw [hcost, if_pos ⟨⟨signature, found, hsignature, hfound⟩, hnotPartnered⟩, add_mul,
          one_mul]
        apply le_of_eq
        ring
      · rw [if_neg hopen, add_zero]
        exact le_add_self
  set rest := ENNReal.ofReal (U - φ) + open₀ * weight
  calc
    _ ≤ ∑' result, Pr[= result | base] * (raceCost S W weight result.1 + rest) := by
      refine ENNReal.tsum_le_tsum fun result => ?_
      by_cases hresult : result ∈ support base
      · exact mul_le_mul' le_rfl (hafter result hresult)
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
    _ = (∑' result, Pr[= result | base] * raceCost S W weight result.1) +
          ∑' result, Pr[= result | base] * rest := by
      rw [← ENNReal.tsum_add]
      exact tsum_congr fun result => mul_add _ _ _
    _ ≤ (∑' result, Pr[= result | base] * raceCost S W weight result.1) + rest := by
      rw [ENNReal.tsum_mul_right]
      exact add_le_add le_rfl ((mul_le_mul' tsum_probOutput_le_one le_rfl).trans_eq (one_mul _))
    _ ≤ ENNReal.ofReal φ + (ENNReal.ofReal (U - φ) + open₀ * weight) := by
      apply add_le_add _ le_rfl
      refine (precomputedSignBoundedAttempts_expectedCost_le secretKey leafIndex message S W
        weight hSW signingAttemptLimit cache hW).trans ?_
      exact raceBound_le_leafPotential hq cache leafIndex message remaining
        (hinv.entries_add_le hsigned)
    _ = potential q secretKey cache trace remaining := by
      rw [potential_of_not_bad hnodup hbad, ← add_assoc,
        ← ENNReal.ofReal_add hφ0 (by linarith), add_sub_cancel]

end Xmss.TargetSum.Direct.Collision
