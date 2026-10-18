import XmssSecurity.Proof.TargetSum.Correctness
import XmssSecurity.Proof.Generic.Seeded.Presampling
import XmssSecurity.Proof.Generic.Deterministic.Inputs
import XmssSecurity.Proof.Generic.EncodingRejectionProbability
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability
/-!
# The probability that all trials of a signing request fail

Fix a public parameter, a master seed, an epoch, and a message. Whatever computation runs in the
random-oracle world, the probability that its final cache shows all `A_max` trials of signing that
message failing (`SigningFails`) is at most `(1 - p + A_max / 2^128)^A_max`
(`probEvent_presampleChain_fails_le`), where `p` is the probability that a uniform digest decodes.
A randomizer is a fresh uniform value, so it repeats an earlier one with probability at most
`A_max / 2^128`; otherwise its digest is a fresh uniform value, which decodes with probability `p`.
Since `p > 2^-15`, this is at most `(1 - 2^-16)^(2^32) ≤ 2^-(2^16)` (`probEvent_signingFails_le`).

The computation may query the inputs of the trials itself, in any order. The proof therefore
appends a check that queries them (`checkTrials`), samples their oracle answers before the
computation runs (`presampleChain`, by `Seeded.evalDist_presample_fresh`), and reads the check's
outcome off the presampled answers.
-/

open OracleComp OracleSpec ENNReal

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.Correct

set_option backward.isDefEq.respectTransparency false

variable (parameter : PublicParameter) (seed : MasterSeed) (leafIndex : LeafIndex)
  (message : Message)

/-- The randomizer input of trial `trial`. -/
abbrev randomizerInput (trial : ℕ) : HashInput :=
  Generic.randomizerHashInput parameter seed leafIndex message (BitVec.ofNat 32 trial)

/-- The digest input of the message under the randomizer read from `output`. -/
abbrev digestInput (output : HashOutput) : HashInput :=
  Concrete.CacheView.encodingInput parameter leafIndex
    (message, output.extractLsb' 0 randomnessBits)

/-! ### Distinct inputs -/

theorem randomizerInput_injective {trial other : ℕ} (htrial : trial < 2 ^ 32)
    (hother : other < 2 ^ 32)
    (h : randomizerInput parameter seed leafIndex message trial =
      randomizerInput parameter seed leafIndex message other) : trial = other := by
  have hbits := (randomizerHashInput_injective h).2.2.2.2
  have := congrArg BitVec.toNat hbits
  simp only [BitVec.toNat_ofNat] at this
  rwa [Nat.mod_eq_of_lt htrial, Nat.mod_eq_of_lt hother] at this

theorem randomizerInput_ne_encodingInput (trial : ℕ) (randomness : Randomness) :
    randomizerInput parameter seed leafIndex message trial ≠
      Concrete.CacheView.encodingInput parameter leafIndex (message, randomness) := by
  intro h
  unfold randomizerInput Generic.randomizerHashInput Concrete.CacheView.encodingInput
    Generic.tweakableHashInput Generic.tweakBytes at h
  simp only [List.append_assoc] at h
  have hfields := fieldBytes_injective (List.append_inj h (by simp [length_fieldBytes])).1
  have htag := congrArg Generic.TweakFields.tag hfields
  simp [Generic.hashDomainFields, Generic.tweakFields] at htag

theorem randomizerInput_ne_digestInput (trial : ℕ) (output : HashOutput) :
    randomizerInput parameter seed leafIndex message trial ≠
      digestInput parameter leafIndex message output :=
  randomizerInput_ne_encodingInput parameter seed leafIndex message trial _

/-! ### The randomizer of a uniform answer is uniform -/

theorem hashOutputBits_eq_randomness : hashOutputBits = 128 + randomnessBits := by decide

/-- A 256-bit oracle answer is equivalently its high 128 bits and its low 128 bits, the
randomizer. -/
def randomnessSplitEquiv : HashOutput ≃ BitVec 128 × Randomness where
  toFun output := ((output.cast hashOutputBits_eq_randomness).extractLsb' randomnessBits 128,
    (output.cast hashOutputBits_eq_randomness).extractLsb' 0 randomnessBits)
  invFun halves := (halves.1 ++ halves.2).cast hashOutputBits_eq_randomness.symm
  left_inv output := by
    simp only
    rw [BitVec.extractLsb'_append_extractLsb']
    simp
  right_inv halves := by
    simp only [BitVec.cast_eq]
    exact Prod.ext BitVec.extractLsb'_append_eq_left BitVec.extractLsb'_append_eq_right

theorem randomnessSplitEquiv_snd (output : HashOutput) :
    (randomnessSplitEquiv output).2 = output.extractLsb' 0 randomnessBits := by
  apply BitVec.eq_of_toNat_eq
  simp [randomnessSplitEquiv, BitVec.extractLsb']

/-- The randomizer read from a uniform answer lands in a set of `T.card` values with probability
`T.card / 2^128`. -/
theorem probEvent_randomness_mem (T : Finset Randomness) :
    Pr[fun output : HashOutput => output.extractLsb' 0 randomnessBits ∈ T | $ᵗ HashOutput] =
      T.card / ((2 ^ randomnessBits : ℕ) : ℝ≥0∞) := by
  classical
  rw [probEvent_uniformSample]
  have hcard : (Finset.univ.filter fun output : HashOutput =>
      output.extractLsb' 0 randomnessBits ∈ T).card = 2 ^ 128 * T.card := by
    rw [← Finset.card_map randomnessSplitEquiv.toEmbedding]
    have hmap : (Finset.univ.filter fun output : HashOutput =>
        output.extractLsb' 0 randomnessBits ∈ T).map randomnessSplitEquiv.toEmbedding =
        (Finset.univ : Finset (BitVec 128)) ×ˢ T := by
      ext pair
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Equiv.toEmbedding_apply, Finset.mem_product]
      constructor
      · rintro ⟨output, houtput, rfl⟩
        rw [randomnessSplitEquiv_snd]
        exact houtput
      · intro hpair
        refine ⟨randomnessSplitEquiv.symm pair, ?_, by simp⟩
        rw [← randomnessSplitEquiv_snd, Equiv.apply_symm_apply]
        exact hpair
    rw [hmap, Finset.card_product, Finset.card_univ]
    simp
  rw [hcard, Rom.card_hashOutput, hashOutputBits_eq_randomness, pow_add, Nat.cast_mul,
    Nat.cast_mul, ENNReal.mul_div_mul_left _ _ (by simp) (by simp)]

/-! ### Checking the trials -/

/-- Query the randomizer and the digest of trials `trial, …, trial + count - 1`, and return
whether every digest fails to decode. -/
noncomputable def checkTrials : ℕ → ℕ → OracleComp OracleWorld Bool
  | 0, _ => pure true
  | count + 1, trial => do
      let randomizerOutput ← (liftM (OracleWorld.query
        (.inr (randomizerInput parameter seed leafIndex message trial))) :
          OracleComp OracleWorld HashOutput)
      let digestOutput ← (liftM (OracleWorld.query
        (.inr (digestInput parameter leafIndex message randomizerOutput))) :
          OracleComp OracleWorld HashOutput)
      if (Code.decodeDigest (Generic.truncateHash digestOutput)).isNone then
        checkTrials count (trial + 1)
      else
        pure false

theorem romImpl_run_cached {input : HashInput} {cache : QueryCache HashSpec}
    {output : HashOutput} (hcached : cache input = some output) :
    (simulateQ romImpl (liftM (OracleWorld.query (.inr input)) :
      OracleComp OracleWorld HashOutput)).run cache = pure (output, cache) := by
  rw [simulateQ_spec_query]
  change (randomOracle (spec := HashSpec) input).run cache = pure (output, cache)
  rw [QueryImpl.withCaching_run_some _ hcached]

/-- When the trials failed in the cache, the check returns `true` and leaves the cache as it
is. -/
theorem checkTrials_run_of_fails :
    ∀ (count trial : ℕ) (cache : QueryCache HashSpec),
      (∀ index < count, TrialFails parameter seed leafIndex message cache (trial + index)) →
      (simulateQ romImpl (checkTrials parameter seed leafIndex message count trial)).run cache =
        pure (true, cache) := by
  intro count
  induction count with
  | zero => intro trial cache _; rfl
  | succ count ih =>
      intro trial cache hfails
      obtain ⟨randomizerOutput, hrandomizer, digestOutput, hdigest, hdecode⟩ :=
        hfails 0 (Nat.succ_pos _)
      simp only [Nat.add_zero] at hrandomizer hdigest
      simp only [checkTrials, simulateQ_bind, StateT.run_bind]
      rw [romImpl_run_cached hrandomizer, pure_bind, romImpl_run_cached hdigest, pure_bind]
      simp only [hdecode, Option.isNone_none, if_true]
      exact ih (trial + 1) cache fun index hindex => by
        simpa [Nat.add_assoc, Nat.add_comm 1] using hfails (index + 1) (by omega)

/-- The event that the trials failed is at most as likely as the appended check returning
`true`. -/
theorem probEvent_signingFails_le_check {α : Type} (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) :
    Pr[fun result => SigningFails parameter seed leafIndex message result.2 |
        (simulateQ romImpl computation).run cache] ≤
      Pr[fun result => result = true | (simulateQ romImpl
        (computation >>= fun _ =>
          checkTrials parameter seed leafIndex message signingAttemptLimit 0)).run' cache] := by
  classical
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind, probEvent_map, probEvent_bind_eq_tsum,
    probEvent_eq_tsum_ite]
  refine ENNReal.tsum_le_tsum fun result => ?_
  split_ifs with hfails
  · rw [checkTrials_run_of_fails parameter seed leafIndex message signingAttemptLimit 0 result.2
      (fun index hindex => by simpa using hfails index hindex)]
    simp
  · exact zero_le

/-! ### Presampling the trials -/

/-- Sample the oracle answers of the trials `trial, …, trial + count - 1` ahead of time: for each
trial its randomizer, and its digest unless that input is already cached. -/
noncomputable def presampleChain : ℕ → ℕ → QueryCache HashSpec → ProbComp (QueryCache HashSpec)
  | 0, _, cache => pure cache
  | count + 1, trial, cache => do
      let randomizerOutput ← $ᵗ HashOutput
      let cacheWithRandomizer := cache.cacheQuery
        (randomizerInput parameter seed leafIndex message trial) randomizerOutput
      match cacheWithRandomizer (digestInput parameter leafIndex message randomizerOutput) with
      | some _ => presampleChain count (trial + 1) cacheWithRandomizer
      | none => do
          let digestOutput ← $ᵗ HashOutput
          presampleChain count (trial + 1) (cacheWithRandomizer.cacheQuery
            (digestInput parameter leafIndex message randomizerOutput) digestOutput)

theorem randomizerInput_fresh_after {trial : ℕ} {cache : QueryCache HashSpec} {count : ℕ}
    (hbound : trial + (count + 1) ≤ 2 ^ 32)
    (hfresh : ∀ index < count + 1,
      cache (randomizerInput parameter seed leafIndex message (trial + index)) = none)
    (randomizerOutput : HashOutput) :
    ∀ index < count, (cache.cacheQuery (randomizerInput parameter seed leafIndex message trial)
      randomizerOutput) (randomizerInput parameter seed leafIndex message (trial + 1 + index)) =
        none := by
  intro index hindex
  have hne : randomizerInput parameter seed leafIndex message (trial + 1 + index) ≠
      randomizerInput parameter seed leafIndex message trial := fun h => by
    have := randomizerInput_injective parameter seed leafIndex message (by omega) (by omega) h
    omega
  rw [QueryCache.cacheQuery_of_ne _ _ hne]
  have := hfresh (index + 1) (by omega)
  rwa [show trial + (index + 1) = trial + 1 + index by omega] at this

/-- Presampling the trials does not change what any computation outputs. -/
theorem evalDist_run'_eq_presampleChain {β : Type} (computation : OracleComp OracleWorld β) :
    ∀ (count trial : ℕ) (cache : QueryCache HashSpec), trial + count ≤ 2 ^ 32 →
      (∀ index < count,
        cache (randomizerInput parameter seed leafIndex message (trial + index)) = none) →
      𝒟[(simulateQ romImpl computation).run' cache] =
        𝒟[presampleChain parameter seed leafIndex message count trial cache >>= fun presampled =>
          (simulateQ romImpl computation).run' presampled]
  | 0, trial, cache, _, _ => by simp [presampleChain]
  | count + 1, trial, cache, hbound, hfresh => by
      rw [Seeded.evalDist_presample_fresh computation cache _ (by simpa using hfresh 0 (by omega))]
      simp only [presampleChain, bind_assoc]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro randomizerOutput
      have hfreshAfter := randomizerInput_fresh_after parameter seed leafIndex message hbound
        hfresh randomizerOutput
      split
      · exact evalDist_run'_eq_presampleChain computation count (trial + 1) _ (by omega)
          hfreshAfter
      · rename_i hnone
        rw [Seeded.evalDist_presample_fresh computation _ _ hnone]
        simp only [bind_assoc]
        apply OracleComp.DeferredSampling.evalDist_bind_congr_left
        intro digestOutput
        refine evalDist_run'_eq_presampleChain computation count (trial + 1) _ (by omega)
          fun index hindex => ?_
        rw [QueryCache.cacheQuery_of_ne _ _
          (randomizerInput_ne_digestInput parameter seed leafIndex message _ _)]
        exact hfreshAfter index hindex

/-- The presampled answers of the trials, randomizer and digest, are all cached. -/
def ChainCached (count trial : ℕ) (cache : QueryCache HashSpec) : Prop :=
  ∀ index < count, ∃ randomizerOutput,
    cache (randomizerInput parameter seed leafIndex message (trial + index)) =
      some randomizerOutput ∧
    ∃ digestOutput, cache (digestInput parameter leafIndex message randomizerOutput) =
      some digestOutput

theorem le_cacheQuery_of_none {cache : QueryCache HashSpec} {input : HashInput}
    (hnone : cache input = none) (output : HashOutput) :
    cache ≤ cache.cacheQuery input output := by
  intro other value hvalue
  have hne : other ≠ input := fun h => by rw [h, hnone] at hvalue; simp at hvalue
  rw [QueryCache.cacheQuery_of_ne _ _ hne]
  exact hvalue

/-- Presampling only adds the trials' answers to the cache. -/
theorem presampleChain_support :
    ∀ (count trial : ℕ) (cache : QueryCache HashSpec), trial + count ≤ 2 ^ 32 →
      (∀ index < count,
        cache (randomizerInput parameter seed leafIndex message (trial + index)) = none) →
      ∀ presampled ∈ support (presampleChain parameter seed leafIndex message count trial cache),
        cache ≤ presampled ∧ ChainCached parameter seed leafIndex message count trial presampled
  | 0, trial, cache, _, _ => by
      intro presampled hpresampled
      simp only [presampleChain, support_pure, Set.mem_singleton_iff] at hpresampled
      subst hpresampled
      exact ⟨le_rfl, fun index hindex => absurd hindex (Nat.not_lt_zero _)⟩
  | count + 1, trial, cache, hbound, hfresh => by
      intro presampled hpresampled
      simp only [presampleChain, mem_support_bind_iff] at hpresampled
      obtain ⟨randomizerOutput, -, hpresampled⟩ := hpresampled
      have hfreshAfter := randomizerInput_fresh_after parameter seed leafIndex message hbound
        hfresh randomizerOutput
      have hrandomizerLe := le_cacheQuery_of_none (hfresh 0 (by omega)) randomizerOutput
      simp only [Nat.add_zero] at hrandomizerLe
      split at hpresampled
      · rename_i digestOutput hcached
        obtain ⟨hle, hchain⟩ := presampleChain_support count (trial + 1) _ (by omega)
          hfreshAfter presampled hpresampled
        refine ⟨hrandomizerLe.trans hle, fun index hindex => ?_⟩
        cases index with
        | zero =>
            refine ⟨randomizerOutput, hle (by simp), digestOutput, hle hcached⟩
        | succ index =>
            have := hchain index (by omega)
            rwa [show trial + 1 + index = trial + (index + 1) by omega] at this
      · rename_i hnone
        simp only [mem_support_bind_iff] at hpresampled
        obtain ⟨digestOutput, -, hpresampled⟩ := hpresampled
        obtain ⟨hle, hchain⟩ := presampleChain_support count (trial + 1) _ (by omega)
          (fun index hindex => by
            rw [QueryCache.cacheQuery_of_ne _ _
              (randomizerInput_ne_digestInput parameter seed leafIndex message _ _)]
            exact hfreshAfter index hindex) presampled hpresampled
        have hdigestLe := le_cacheQuery_of_none hnone digestOutput
        refine ⟨hrandomizerLe.trans (hdigestLe.trans hle), fun index hindex => ?_⟩
        cases index with
        | zero =>
            refine ⟨randomizerOutput, (hdigestLe.trans hle) (by simp), digestOutput,
              hle (by simp)⟩
        | succ index =>
            have := hchain index (by omega)
            rwa [show trial + 1 + index = trial + (index + 1) by omega] at this

/-! ### The check reads the presampled answers -/

/-- From any cache above presampled answers, the check returns `true` only if the presampled
trials all failed. -/
theorem checkTrials_true_of_cached :
    ∀ (count trial : ℕ) (presampled cache : QueryCache HashSpec), presampled ≤ cache →
      ChainCached parameter seed leafIndex message count trial presampled →
      ∀ result ∈ support ((simulateQ romImpl
          (checkTrials parameter seed leafIndex message count trial)).run cache),
        result.1 = true →
          ∀ index < count, TrialFails parameter seed leafIndex message presampled (trial + index) := by
  intro count
  induction count with
  | zero => intro _ _ _ _ _ _ _ _ index hindex; exact absurd hindex (Nat.not_lt_zero _)
  | succ count ih =>
      intro trial presampled cache hle hchain result hresult htrue
      obtain ⟨randomizerOutput, hrandomizer, digestOutput, hdigest⟩ := hchain 0 (Nat.succ_pos _)
      simp only [Nat.add_zero] at hrandomizer
      simp only [checkTrials, simulateQ_bind, StateT.run_bind] at hresult
      rw [romImpl_run_cached (hle hrandomizer), pure_bind, romImpl_run_cached (hle hdigest),
        pure_bind] at hresult
      cases hdecode : Code.decodeDigest (Generic.truncateHash digestOutput) with
      | some encoding =>
          simp only [hdecode, Option.isNone_some, Bool.false_eq_true, if_false, simulateQ_pure,
            StateT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
          rw [hresult] at htrue
          simp at htrue
      | none =>
          simp only [hdecode, Option.isNone_none, if_true] at hresult
          have hrest := ih (trial + 1) presampled cache hle (fun index hindex => by
            have := hchain (index + 1) (by omega)
            rwa [show trial + (index + 1) = trial + 1 + index by omega] at this) result hresult htrue
          intro index hindex
          cases index with
          | zero => exact ⟨randomizerOutput, hrandomizer, digestOutput, hdigest, hdecode⟩
          | succ index =>
              have := hrest index (by omega)
              rwa [show trial + 1 + index = trial + (index + 1) by omega] at this

/-- The event that the trials failed, after any computation run from the empty cache, is at most
as likely as the presampled trials all failing. -/
theorem probEvent_signingFails_le_presampled {α : Type} (computation : OracleComp OracleWorld α) :
    Pr[fun result => SigningFails parameter seed leafIndex message result.2 |
        (simulateQ romImpl computation).run ∅] ≤
      Pr[fun presampled => ∀ index < signingAttemptLimit,
          TrialFails parameter seed leafIndex message presampled index |
        presampleChain parameter seed leafIndex message signingAttemptLimit 0 ∅] := by
  classical
  refine (probEvent_signingFails_le_check parameter seed leafIndex message computation ∅).trans ?_
  rw [probEvent_congr' (fun _ _ => Iff.rfl)
    (evalDist_run'_eq_presampleChain parameter seed leafIndex message
      (computation >>= fun _ => checkTrials parameter seed leafIndex message signingAttemptLimit 0)
      signingAttemptLimit 0 ∅ (by simp [signingAttemptLimit]) (fun _ _ => rfl)),
    probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  refine ENNReal.tsum_le_tsum fun presampled => ?_
  by_cases hsupport : presampled ∈ support
      (presampleChain parameter seed leafIndex message signingAttemptLimit 0 ∅)
  · obtain ⟨-, hchain⟩ := presampleChain_support parameter seed leafIndex message
      signingAttemptLimit 0 ∅ (by simp [signingAttemptLimit]) (fun _ _ => rfl) presampled hsupport
    split_ifs with hfails
    · exact mul_le_of_le_one_right' probEvent_le_one
    · rw [probEvent_eq_zero (fun result hresult htrue => hfails fun index hindex => ?_), mul_zero]
      rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind, support_map, Set.mem_image] at hresult
      obtain ⟨⟨checked, finalCache⟩, hchecked, rfl⟩ := hresult
      rw [mem_support_bind_iff] at hchecked
      obtain ⟨⟨_, middleCache⟩, hmiddle, hchecked⟩ := hchecked
      simpa using checkTrials_true_of_cached parameter seed leafIndex message signingAttemptLimit
        0 presampled middleCache (xmssRom_cache_le computation presampled _ hmiddle) hchain _
        hchecked htrue index hindex
  · rw [probOutput_eq_zero_of_not_mem_support hsupport, zero_mul]
    exact zero_le

/-! ### The presampled trials all fail with small probability -/

/-- The randomizers whose digest input is cached. -/
noncomputable def cachedRandomizers (cache : QueryCache HashSpec) : Finset Randomness :=
  Finset.univ.filter fun randomness =>
    cache (Concrete.CacheView.encodingInput parameter leafIndex (message, randomness)) ≠ none

theorem cachedRandomizers_cacheQuery_randomizer (cache : QueryCache HashSpec) (trial : ℕ)
    (output : HashOutput) :
    cachedRandomizers parameter leafIndex message
        (cache.cacheQuery (randomizerInput parameter seed leafIndex message trial) output) =
      cachedRandomizers parameter leafIndex message cache := by
  ext randomness
  simp only [cachedRandomizers, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [QueryCache.cacheQuery_of_ne _ _
    (randomizerInput_ne_encodingInput parameter seed leafIndex message trial randomness).symm]

theorem card_cachedRandomizers_cacheQuery_le (cache : QueryCache HashSpec) (input : HashInput)
    (output : HashOutput) (randomness : Randomness)
    (hinput : input = Concrete.CacheView.encodingInput parameter leafIndex (message, randomness)) :
    (cachedRandomizers parameter leafIndex message (cache.cacheQuery input output)).card ≤
      (cachedRandomizers parameter leafIndex message cache).card + 1 := by
  classical
  refine (Finset.card_le_card fun other hother => ?_).trans (Finset.card_insert_le randomness _)
  simp only [cachedRandomizers, Finset.mem_filter, Finset.mem_univ, true_and] at hother
  rw [Finset.mem_insert]
  by_cases heq : other = randomness
  · exact Or.inl heq
  · refine Or.inr ?_
    simp only [cachedRandomizers, Finset.mem_filter, Finset.mem_univ, true_and]
    have hne : Concrete.CacheView.encodingInput parameter leafIndex (message, other) ≠ input := by
      rw [hinput]
      intro h
      exact heq (Concrete.CacheView.encodingInput_injective parameter leafIndex h |>
        congrArg Prod.snd)
    rwa [QueryCache.cacheQuery_of_ne _ _ hne] at hother

theorem probEvent_invalid_uniform :
    Pr[fun output : HashOutput => Code.decodeDigest (Generic.truncateHash output) = none |
      $ᵗ HashOutput] = 1 - TargetSum.acceptanceProbability := by
  rw [← code_acceptanceProbability, ← Code.probEvent_invalidDigest_uniformHashOutput]
  congr 1
  funext output
  simp [Code.ValidDigest, Option.eq_none_iff_forall_ne_some]

/-- Each presampled trial fails with probability at most `1 - p` plus the chance that its
randomizer hits a cached digest input. -/
theorem probEvent_presampleChain_fails_le :
    ∀ (count trial : ℕ) (cache : QueryCache HashSpec) (bound : ℕ), trial + count ≤ 2 ^ 32 →
      (∀ index < count,
        cache (randomizerInput parameter seed leafIndex message (trial + index)) = none) →
      (cachedRandomizers parameter leafIndex message cache).card ≤ bound →
      Pr[fun presampled => ∀ index < count,
          TrialFails parameter seed leafIndex message presampled (trial + index) |
        presampleChain parameter seed leafIndex message count trial cache] ≤
      (1 - TargetSum.acceptanceProbability +
        ((bound + count : ℕ) : ℝ≥0∞) / ((2 ^ randomnessBits : ℕ) : ℝ≥0∞)) ^ count := by
  intro count
  induction count with
  | zero => intro _ _ _ _ _ _; exact probEvent_le_one.trans (le_of_eq (pow_zero _).symm)
  | succ count ih =>
      intro trial cache bound hbound hfresh hcard
      classical
      set rest : ℝ≥0∞ := (1 - TargetSum.acceptanceProbability +
        ((bound + 1 + count : ℕ) : ℝ≥0∞) / ((2 ^ randomnessBits : ℕ) : ℝ≥0∞)) ^ count with hrest
      -- the bound for the remaining trials, from any cache with one more cached digest
      have hrestBound : ∀ (other : QueryCache HashSpec),
          (∀ index < count,
            other (randomizerInput parameter seed leafIndex message (trial + 1 + index)) = none) →
          (cachedRandomizers parameter leafIndex message other).card ≤ bound + 1 →
          Pr[fun presampled => ∀ index < count,
              TrialFails parameter seed leafIndex message presampled (trial + 1 + index) |
            presampleChain parameter seed leafIndex message count (trial + 1) other] ≤ rest := by
        intro other hotherFresh hotherCard
        have := ih (trial + 1) other (bound + 1) (by omega) hotherFresh hotherCard
        simpa [hrest, Nat.add_assoc, Nat.add_comm 1] using this
      have hstep : ∀ randomizerOutput : HashOutput,
          Pr[fun presampled => ∀ index < count + 1,
              TrialFails parameter seed leafIndex message presampled (trial + index) |
            (match (cache.cacheQuery (randomizerInput parameter seed leafIndex message trial)
                randomizerOutput) (digestInput parameter leafIndex message randomizerOutput) with
              | some _ => presampleChain parameter seed leafIndex message count (trial + 1)
                  (cache.cacheQuery (randomizerInput parameter seed leafIndex message trial)
                    randomizerOutput)
              | none => do
                  let digestOutput ← $ᵗ HashOutput
                  presampleChain parameter seed leafIndex message count (trial + 1)
                    ((cache.cacheQuery (randomizerInput parameter seed leafIndex message trial)
                      randomizerOutput).cacheQuery
                        (digestInput parameter leafIndex message randomizerOutput) digestOutput))] ≤
            (if randomizerOutput.extractLsb' 0 randomnessBits ∈
                cachedRandomizers parameter leafIndex message cache then rest else 0) +
              (1 - TargetSum.acceptanceProbability) * rest := by
        intro randomizerOutput
        have hfreshAfter := randomizerInput_fresh_after parameter seed leafIndex message hbound
          hfresh randomizerOutput
        have hcard₁ := cachedRandomizers_cacheQuery_randomizer parameter seed leafIndex message
          cache trial randomizerOutput
        have hshift : ∀ presampled : QueryCache HashSpec,
            (∀ index < count + 1,
              TrialFails parameter seed leafIndex message presampled (trial + index)) →
            ∀ index < count,
              TrialFails parameter seed leafIndex message presampled (trial + 1 + index) :=
          fun presampled hall index hindex => by
            have := hall (index + 1) (by omega)
            rwa [show trial + (index + 1) = trial + 1 + index by omega] at this
        split
        · rename_i digestOutput hcached
          have hmem : randomizerOutput.extractLsb' 0 randomnessBits ∈
              cachedRandomizers parameter leafIndex message cache := by
            rw [← hcard₁]
            simp only [cachedRandomizers, Finset.mem_filter, Finset.mem_univ, true_and]
            change (cache.cacheQuery _ randomizerOutput)
              (digestInput parameter leafIndex message randomizerOutput) ≠ none
            rw [hcached]
            simp
          rw [if_pos hmem]
          refine le_add_right ((probEvent_mono fun presampled _ hall =>
            hshift presampled hall).trans (hrestBound _ hfreshAfter ?_))
          rw [hcard₁]
          omega
        · rename_i hnone
          refine le_add_left ?_
          rw [probEvent_bind_eq_tsum]
          calc
            ∑' digestOutput, Pr[= digestOutput | $ᵗ HashOutput] *
                Pr[fun presampled => ∀ index < count + 1,
                  TrialFails parameter seed leafIndex message presampled (trial + index) |
                presampleChain parameter seed leafIndex message count (trial + 1)
                  ((cache.cacheQuery (randomizerInput parameter seed leafIndex message trial)
                    randomizerOutput).cacheQuery
                      (digestInput parameter leafIndex message randomizerOutput) digestOutput)] ≤
              ∑' digestOutput, Pr[= digestOutput | $ᵗ HashOutput] *
                (if Code.decodeDigest (Generic.truncateHash digestOutput) = none then rest
                  else 0) := by
              refine ENNReal.tsum_le_tsum fun digestOutput => mul_le_mul_right ?_ _
              have hfresh₂ : ∀ index < count,
                  ((cache.cacheQuery (randomizerInput parameter seed leafIndex message trial)
                    randomizerOutput).cacheQuery
                      (digestInput parameter leafIndex message randomizerOutput) digestOutput)
                    (randomizerInput parameter seed leafIndex message (trial + 1 + index)) =
                    none := fun index hindex => by
                rw [QueryCache.cacheQuery_of_ne _ _
                  (randomizerInput_ne_digestInput parameter seed leafIndex message _ _)]
                exact hfreshAfter index hindex
              split_ifs with hdecode
              · refine (probEvent_mono fun presampled _ hall =>
                  hshift presampled hall).trans (hrestBound _ hfresh₂ ?_)
                refine (card_cachedRandomizers_cacheQuery_le parameter leafIndex message _ _
                  digestOutput (randomizerOutput.extractLsb' 0 randomnessBits) rfl).trans ?_
                rw [hcard₁]
                omega
              · refine le_of_eq (probEvent_eq_zero fun presampled hpresampled hall => ?_)
                obtain ⟨hle, -⟩ := presampleChain_support parameter seed leafIndex message count
                  (trial + 1) _ (by omega) hfresh₂ presampled hpresampled
                obtain ⟨randomizerOutput', hrandomizer', digestOutput', hdigest', hdecode'⟩ :=
                  hall 0 (Nat.succ_pos _)
                simp only [Nat.add_zero] at hrandomizer'
                have hrandomizerEq : randomizerOutput' = randomizerOutput := by
                  have h₁ := hle (show ((cache.cacheQuery
                      (randomizerInput parameter seed leafIndex message trial)
                      randomizerOutput).cacheQuery
                        (digestInput parameter leafIndex message randomizerOutput) digestOutput)
                      (randomizerInput parameter seed leafIndex message trial) =
                      some randomizerOutput by
                    rw [QueryCache.cacheQuery_of_ne _ _
                      (randomizerInput_ne_digestInput parameter seed leafIndex message _ _)]
                    simp)
                  rw [hrandomizer'] at h₁
                  exact Option.some.inj h₁
                subst hrandomizerEq
                have h₂ := hle (show ((cache.cacheQuery
                    (randomizerInput parameter seed leafIndex message trial)
                    randomizerOutput').cacheQuery
                      (digestInput parameter leafIndex message randomizerOutput') digestOutput)
                    (digestInput parameter leafIndex message randomizerOutput') =
                    some digestOutput by simp)
                rw [hdigest'] at h₂
                rw [Option.some.inj h₂] at hdecode'
                exact hdecode hdecode'
            _ = Pr[fun output : HashOutput =>
                  Code.decodeDigest (Generic.truncateHash output) = none | $ᵗ HashOutput] * rest := by
              rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
              congr 1
              funext digestOutput
              split_ifs <;> simp
            _ = (1 - TargetSum.acceptanceProbability) * rest := by rw [probEvent_invalid_uniform]
      simp only [presampleChain]
      rw [probEvent_bind_eq_tsum]
      calc
        _ ≤ ∑' randomizerOutput, Pr[= randomizerOutput | $ᵗ HashOutput] *
              ((if randomizerOutput.extractLsb' 0 randomnessBits ∈
                  cachedRandomizers parameter leafIndex message cache then rest else 0) +
                (1 - TargetSum.acceptanceProbability) * rest) :=
          ENNReal.tsum_le_tsum fun randomizerOutput => mul_le_mul_right (hstep randomizerOutput) _
        _ ≤ Pr[fun output : HashOutput => output.extractLsb' 0 randomnessBits ∈
                cachedRandomizers parameter leafIndex message cache | $ᵗ HashOutput] * rest +
              (1 - TargetSum.acceptanceProbability) * rest := by
          simp only [mul_add]
          rw [ENNReal.tsum_add]
          refine add_le_add (le_of_eq ?_) ?_
          · rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
            refine tsum_congr fun randomizerOutput => ?_
            split_ifs <;> simp
          · rw [ENNReal.tsum_mul_right]
            calc
              _ ≤ 1 * ((1 - TargetSum.acceptanceProbability) * rest) :=
                mul_le_mul_left tsum_probOutput_le_one _
              _ = _ := one_mul _
        _ ≤ ((bound : ℝ≥0∞) / ((2 ^ randomnessBits : ℕ) : ℝ≥0∞)) * rest +
              (1 - TargetSum.acceptanceProbability) * rest := by
          rw [probEvent_randomness_mem]
          gcongr
        _ = (1 - TargetSum.acceptanceProbability +
              (bound : ℝ≥0∞) / ((2 ^ randomnessBits : ℕ) : ℝ≥0∞)) * rest := by ring
        _ ≤ (1 - TargetSum.acceptanceProbability +
              ((bound + (count + 1) : ℕ) : ℝ≥0∞) / ((2 ^ randomnessBits : ℕ) : ℝ≥0∞)) * rest := by
          gcongr
          exact_mod_cast Nat.le_add_right bound (count + 1)
        _ = _ := by
          rw [hrest, show bound + 1 + count = bound + (count + 1) by omega, pow_succ, mul_comm]

/-! ### All trials of a request fail with negligible probability -/

theorem one_div_two_pow_le_one (bits : ℕ) : (1 : ℝ≥0∞) / ((2 ^ bits : ℕ) : ℝ≥0∞) ≤ 1 :=
  ENNReal.div_le_of_le_mul (by rw [one_mul]; exact_mod_cast Nat.one_le_two_pow)

/-- A trial fails with probability at most `1 - 2^-16`, since `p > 2^-15` and a randomizer
repeats with probability at most `A_max / 2^128`. -/
theorem trialFailure_le :
    1 - TargetSum.acceptanceProbability +
        ((signingAttemptLimit : ℕ) : ℝ≥0∞) / ((2 ^ randomnessBits : ℕ) : ℝ≥0∞) ≤
      1 - 1 / ((2 ^ 16 : ℕ) : ℝ≥0∞) := by
  calc
    _ ≤ 1 - 1 / ((2 ^ 15 : ℕ) : ℝ≥0∞) +
        ((signingAttemptLimit : ℕ) : ℝ≥0∞) / ((2 ^ randomnessBits : ℕ) : ℝ≥0∞) := by
      gcongr
      exact TargetSum.acceptanceProbability_lower.le
    _ ≤ _ := by
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      rw [ENNReal.toReal_add (by finiteness) (by finiteness),
        ENNReal.toReal_sub_of_le (one_div_two_pow_le_one 15) ENNReal.one_ne_top,
        ENNReal.toReal_sub_of_le (one_div_two_pow_le_one 16) ENNReal.one_ne_top]
      norm_num [signingAttemptLimit, randomnessBits, ENNReal.toReal_div]

/-- `(1 - 2^-16)^(2^32) ≤ 2^-(2^16)`, from `(1 - 2^-16)^(2^16) ≤ 1/2`. -/
theorem trialFailure_pow_le :
    (1 - 1 / ((2 ^ 16 : ℕ) : ℝ≥0∞)) ^ signingAttemptLimit ≤ (1 / 2) ^ (2 ^ 16) := by
  rw [show signingAttemptLimit = 2 ^ 16 * 2 ^ 16 by norm_num [signingAttemptLimit], pow_mul]
  gcongr
  refine (Code.rejection_power_le _ (one_div_two_pow_le_one 16) _).trans (le_of_eq ?_)
  rw [mul_one_div, ENNReal.div_self (by simp) (by simp), one_add_one_eq_two]

/-- Whatever computation runs, the probability that its final cache shows all trials of a
signing request failing is at most `2^-(2^16)`. -/
theorem probEvent_signingFails_le {α : Type} (computation : OracleComp OracleWorld α) :
    Pr[fun result => SigningFails parameter seed leafIndex message result.2 |
      (simulateQ romImpl computation).run ∅] ≤ (1 / 2) ^ (2 ^ 16) := by
  have hchain := probEvent_presampleChain_fails_le parameter seed leafIndex message
    signingAttemptLimit 0 ∅ 0 (by simp [signingAttemptLimit]) (fun _ _ => by simp)
    (by simp [cachedRandomizers])
  simp only [zero_add] at hchain
  exact (probEvent_signingFails_le_presampled parameter seed leafIndex message computation).trans
    (hchain.trans ((pow_le_pow_left' trialFailure_le _).trans trialFailure_pow_le))

/-! ### The correctness error -/

theorem card_requestTuples :
    Fintype.card (PublicParameter × MasterSeed × LeafIndex × Message) = 2 ^ 672 := by
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_prod, card_bitVec, card_bitVec,
    card_bitVec, Fintype.card_fin, lifetime, ← pow_add, ← pow_add, ← pow_add]
  norm_num [publicParameterBits, treeHeight, messageBits]

theorem union_numeric : (2 : ℝ≥0∞) ^ 672 * (1 / 2) ^ (2 ^ 16) = 1 / 2 ^ 64864 := by
  rw [one_div, one_div, show (2 : ℕ) ^ 16 = 672 + 64864 by norm_num, pow_add, ← mul_assoc,
    ← mul_pow, ENNReal.mul_inv_cancel (by simp) (by simp), one_pow, one_mul, ENNReal.inv_pow]

end XmssSecurity.TargetSum.Correct
