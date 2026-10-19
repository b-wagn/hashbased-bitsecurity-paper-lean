import XmssSecurity.Proof.TargetSum.Direct.CollisionPotential
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-!
# A signing request against the collision potential

The signer caches decodable digests only where it accepts: every encoding input it newly caches
with a decodable digest is the input of the returned signature
(`precomputedSignBoundedAttempts_newValid`). Hence a cached decodable input keeps the partners
it had before the request. The race lemma then bounds the expected cost of the request, `1` for
accepting a cached input with a partner and `w` for one without, by the epoch's potential
(`raceBound_le_leafPotential`).
-/

set_option maxHeartbeats 800000
set_option linter.constructorNameAsVariable false

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open XmssSecurity.Generic

attribute [local irreducible] XmssSecurity.TargetSum.decodeDigest

namespace XmssSecurity.TargetSum.Direct.Collision

open CollisionMath

/-- What the bounded-attempt signer leaves in the cache: the cache only grows, the returned
signature's input is cached with a decodable digest, and every other newly cached encoding input
of the epoch has an undecodable digest. -/
theorem precomputedSignBoundedAttempts_newValid (secretKey : Generic.SecretKey) (leafIndex : LeafIndex)
    (message : Message) :
    ∀ (attempts : ℕ) (cache : QueryCache HashSpec)
      (result : Option Generic.Signature × QueryCache HashSpec),
      result ∈ support ((simulateQ romImpl
        (Concrete.precomputedSignBoundedAttempts attempts secretKey leafIndex message)).run
          cache) →
      cache ≤ result.2 ∧
      (∀ signature, result.1 = some signature →
        IsValid secretKey.parameter result.2 leafIndex (message, signature.randomness)) ∧
      ∀ entry, cache (input secretKey.parameter leafIndex entry) = none →
        IsValid secretKey.parameter result.2 leafIndex entry →
          ∃ signature, result.1 = some signature ∧ entry = (message, signature.randomness) := by
  intro attempts
  induction attempts with
  | zero =>
      intro cache result hresult
      simp only [Concrete.precomputedSignBoundedAttempts, simulateQ_pure, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at hresult
      subst hresult
      refine ⟨le_rfl, fun signature h => by simp at h, ?_⟩
      intro entry hnone hvalid
      obtain ⟨output, hcache, _⟩ := hvalid
      change cache (input secretKey.parameter leafIndex entry) = some output at hcache
      rw [hnone] at hcache
      simp at hcache
  | succ attempts ih =>
      intro cache result hresult
      rw [Concrete.precomputedSignBoundedAttempts_run_succ_eq, mem_support_bind_iff] at hresult
      obtain ⟨randomness, -, hrest⟩ := hresult
      rw [mem_support_bind_iff] at hrest
      obtain ⟨attempt, hattempt, hcont⟩ := hrest
      set attemptInput := input secretKey.parameter leafIndex (message, randomness)
      -- the attempt either reads a cached digest or samples a fresh one
      have hcases : (attempt.2 = cache ∧
            ∃ output, cache attemptInput = some output ∧
              attempt.1 = (Code.decodeDigest (output)).map
                (Generic.Concrete.precomputedSignWithEncoding secretKey leafIndex randomness)) ∨
          (cache attemptInput = none ∧ ∃ output, attempt.2 = cache.cacheQuery attemptInput output ∧
              attempt.1 = (Code.decodeDigest (output)).map
                (Generic.Concrete.precomputedSignWithEncoding secretKey leafIndex randomness)) := by
        cases hcached : cache attemptInput with
        | some output =>
            rw [Concrete.precomputedSignAttempt_run_cached secretKey leafIndex message randomness
              cache output hcached, support_pure, Set.mem_singleton_iff] at hattempt
            subst hattempt
            exact Or.inl ⟨rfl, output, rfl, rfl⟩
        | none =>
            rw [Concrete.precomputedSignAttempt_run_fresh secretKey leafIndex message randomness
              cache hcached, support_map] at hattempt
            obtain ⟨output, -, houtput⟩ := hattempt
            subst houtput
            exact Or.inr ⟨rfl, output, rfl, rfl⟩
      -- the continuation either stops or runs the remaining attempts
      cases hanswer : attempt.1 with
      | some signature =>
          have hstop : result = (some signature, attempt.2) := by
            have : result ∈ support (pure (some signature, attempt.2) :
                ProbComp (Option Generic.Signature × QueryCache HashSpec)) := by
              simpa [Concrete.precomputedSignBoundedAttemptsContinuation, hanswer] using hcont
            simpa using this
          subst hstop
          have hrandomness : signature.randomness = randomness := by
            rcases hcases with ⟨_, output, _, hmap⟩ | ⟨_, output, _, hmap⟩ <;>
            · rw [hanswer] at hmap
              cases hdecode : Code.decodeDigest (output) <;>
                simp [hdecode, Generic.Concrete.precomputedSignWithEncoding] at hmap
              subst hmap
              rfl
          rcases hcases with ⟨hcacheEq, output, houtput, hmap⟩ | ⟨hfresh, output, hcacheEq, hmap⟩
          · refine ⟨le_of_eq hcacheEq.symm, ?_, ?_⟩
            · intro found hfound
              simp only [Option.some.injEq] at hfound
              subst hfound
              rw [hrandomness, hcacheEq]
              refine ⟨output, houtput, ?_⟩
              rw [hanswer] at hmap
              cases hdecode : Code.decodeDigest (output) with
              | some encoding => exact ⟨encoding, hdecode⟩
              | none => simp [hdecode] at hmap
            · intro entry hnone hvalid
              obtain ⟨found, hfound, _⟩ := hvalid
              rw [hcacheEq, hnone] at hfound
              simp at hfound
          · have hle : cache ≤ attempt.2 := by
              rw [hcacheEq]; exact QueryCache.le_cacheQuery _ hfresh
            refine ⟨hle, ?_, ?_⟩
            · intro found hfound
              simp only [Option.some.injEq] at hfound
              subst hfound
              rw [hrandomness, hcacheEq]
              refine ⟨output, by simp [attemptInput], ?_⟩
              rw [hanswer] at hmap
              cases hdecode : Code.decodeDigest (output) with
              | some encoding => exact ⟨encoding, hdecode⟩
              | none => simp [hdecode] at hmap
            · intro entry hnone _hvalid
              refine ⟨signature, rfl, ?_⟩
              by_contra hne
              obtain ⟨found, hfound, _⟩ := _hvalid
              rw [hcacheEq] at hfound
              have hneInput : input secretKey.parameter leafIndex entry ≠ attemptInput := by
                intro heq
                apply hne
                rw [hrandomness]
                exact Concrete.CacheView.encodingInput_injective _ _ heq
              rw [QueryCache.cacheQuery_of_ne _ _ hneInput, hnone] at hfound
              simp at hfound
      | none =>
          have hcont' : result ∈ support ((simulateQ romImpl
              (Concrete.precomputedSignBoundedAttempts attempts secretKey leafIndex message)).run
                attempt.2) := by
            simpa [Concrete.precomputedSignBoundedAttemptsContinuation, hanswer] using hcont
          obtain ⟨hle, hreturned, hnew⟩ := ih attempt.2 result hcont'
          rcases hcases with ⟨hcacheEq, _⟩ | ⟨hfresh, output, hcacheEq, hmap⟩
          · rw [hcacheEq] at hle hnew
            exact ⟨hle, hreturned, hnew⟩
          · have hle' : cache ≤ attempt.2 := by
              rw [hcacheEq]; exact QueryCache.le_cacheQuery _ hfresh
            refine ⟨hle'.trans hle, hreturned, ?_⟩
            intro entry hnone hvalid
            by_cases hentry : entry = (message, randomness)
            · -- the attempted input carries an undecodable digest
              exfalso
              subst hentry
              obtain ⟨found, hfound, hfoundValid⟩ := hvalid
              have hattemptCache : attempt.2 attemptInput = some output := by
                rw [hcacheEq]; simp [attemptInput]
              have := hle hattemptCache
              rw [show input secretKey.parameter leafIndex (message, randomness) = attemptInput
                from rfl, this, Option.some.injEq] at hfound
              subst hfound
              rw [hanswer] at hmap
              obtain ⟨encoding, hencoding⟩ := hfoundValid
              simp [hencoding] at hmap
            · apply hnew entry _ hvalid
              rw [hcacheEq]
              have hneInput : input secretKey.parameter leafIndex entry ≠ attemptInput := by
                intro heq
                exact hentry (Concrete.CacheView.encodingInput_injective _ _ heq)
              rw [QueryCache.cacheQuery_of_ne _ _ hneInput]
              exact hnone

variable {q : ℕ} {parameter : PublicParameter}

/-- The cached decodable randomizers of a message whose digest another cached encoding input of
the epoch shares. -/
noncomputable def partneredRandomizers (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (leafIndex : LeafIndex) (message : Message) : Finset Randomness := by
  classical
  exact Finset.univ.filter fun randomness => IsPartnered parameter cache leafIndex (message, randomness)

theorem mem_partneredRandomizers {cache : QueryCache HashSpec} {leafIndex : LeafIndex}
    {message : Message} {randomness : Randomness} :
    randomness ∈ partneredRandomizers parameter cache leafIndex message ↔
      IsPartnered parameter cache leafIndex (message, randomness) := by
  classical
  simp [partneredRandomizers]

theorem partneredRandomizers_subset (cache : QueryCache HashSpec) (leafIndex : LeafIndex)
    (message : Message) :
    partneredRandomizers parameter cache leafIndex message ⊆
      validRandomizers parameter cache leafIndex message := by
  classical
  intro randomness hrandomness
  rw [mem_partneredRandomizers] at hrandomness
  simp only [validRandomizers, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hrandomness.isValid

theorem card_partneredRandomizers_le (cache : QueryCache HashSpec) (leafIndex : LeafIndex)
    (message : Message) :
    (partneredRandomizers parameter cache leafIndex message).card ≤
      (partneredEntries parameter cache leafIndex).ncard := by
  classical
  rw [← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard_of_injOn (fun randomness => (message, randomness)) ?_ ?_
  · intro randomness hrandomness
    exact mem_partneredRandomizers.mp hrandomness
  · intro left _ right _ heq
    exact congrArg Prod.snd heq

/-- The race bound of a request at an epoch not yet signed is at most the epoch's potential, when
the weight of a cached input without a partner is `(r + 1)/N` and the epoch's cached inputs and
the `r` remaining queries number at most `q`. -/
theorem raceBound_le_leafPotential (hq : q + 1 ≤ 2 ^ 127) (cache : QueryCache HashSpec)
    (leafIndex : LeafIndex) (message : Message) (remaining : ℕ)
    (hremaining : (entries parameter cache leafIndex).ncard + remaining ≤ q) :
    raceBound (partneredRandomizers parameter cache leafIndex message)
        (validRandomizers parameter cache leafIndex message)
        (ENNReal.ofReal (((remaining : ℝ) + 1) / realN))
        (cachedRandomizersAt parameter leafIndex message cache).card signingAttemptLimit ≤
      ENNReal.ofReal (leafPotential q parameter cache leafIndex) := by
  classical
  have h := hyp q hq
  set S := partneredRandomizers parameter cache leafIndex message
  set W := validRandomizers parameter cache leafIndex message
  set cached := cachedRandomizersAt parameter leafIndex message cache
  have hSW : S ⊆ W := partneredRandomizers_subset cache leafIndex message
  have hSWcard : S.card ≤ W.card := Finset.card_le_card hSW
  have hnK : cached.card ≤ (entries parameter cache leafIndex).ncard :=
    card_cachedRandomizersAt_le_ncard_entries message
  have hKq : (entries parameter cache leafIndex).ncard ≤ q := by omega
  have hnbound : cached.card + signingAttemptLimit ≤ 2 ^ digestBits := by
    have : q ≤ 2 ^ 127 := by omega
    have hsig : signingAttemptLimit = 2 ^ 32 := rfl
    rw [hsig, show digestBits = 128 from rfl]
    omega
  have hN : 0 < realN := by unfold realN; positivity
  have hDn : 0 < realD - cached.card := by
    have : (cached.card : ℝ) ≤ 2 ^ 127 := by
      have : cached.card ≤ 2 ^ 127 := by omega
      exact_mod_cast this
    unfold realD
    linarith
  have hden : 0 < (W.card : ℝ) + realP * (realD - cached.card) :=
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) (mul_pos realP_pos hDn)
  set w : ℝ := ((remaining : ℝ) + 1) / realN
  have hw : 0 ≤ w := div_nonneg (add_nonneg (Nat.cast_nonneg _) zero_le_one) hN.le
  have hdenEq : (W.card : ℝ≥0∞) + TargetSum.acceptanceProbability *
      ((2 ^ digestBits - cached.card - signingAttemptLimit : ℕ) : ℝ≥0∞) =
        ENNReal.ofReal ((W.card : ℝ) + realP * (realD - cached.card)) := by
    have hsub : ((2 ^ digestBits - cached.card - signingAttemptLimit : ℕ) : ℝ) =
        realD - cached.card := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      unfold realD
      simp only [show digestBits = 128 from rfl, show signingAttemptLimit = 2 ^ 32 from rfl]
      push_cast
      ring
    rw [ENNReal.ofReal_add (Nat.cast_nonneg _) (mul_nonneg realP_pos.le hDn.le),
      ENNReal.ofReal_mul realP_pos.le, ofReal_realP, ENNReal.ofReal_natCast, ← hsub,
      ENNReal.ofReal_natCast]
  have hnumEq : (S.card : ℝ≥0∞) + ENNReal.ofReal w * ((W \ S).card : ℝ≥0∞) =
      ENNReal.ofReal ((S.card : ℝ) + w * ((W.card : ℝ) - S.card)) := by
    have hcard : ((W \ S).card : ℝ) = (W.card : ℝ) - S.card := by
      rw [Finset.card_sdiff_of_subset hSW, Nat.cast_sub hSWcard]
    rw [ENNReal.ofReal_add (Nat.cast_nonneg _) (mul_nonneg hw (by rw [← hcard]; exact Nat.cast_nonneg _)),
      ENNReal.ofReal_mul hw, ← hcard, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  unfold raceBound
  rw [hdenEq, hnumEq, ← ENNReal.ofReal_div_of_pos hden]
  apply ENNReal.ofReal_le_ofReal
  have hrace := race_le_leaf h (K := (entries parameter cache leafIndex).ncard)
    (V := (validEntries parameter cache leafIndex).ncard)
    (C := (partneredEntries parameter cache leafIndex).ncard)
    (n := cached.card) (v := W.card) (s := S.card) (w := w)
    (by have : ((entries parameter cache leafIndex).ncard : ℝ) ≤ q := by exact_mod_cast hKq
        linarith)
    (Nat.cast_nonneg _) (by exact_mod_cast hnK) (Nat.cast_nonneg _) (by exact_mod_cast hSWcard)
    (by exact_mod_cast card_partneredRandomizers_le cache leafIndex message)
    (by exact_mod_cast card_validRandomizers_le_ncard_validEntries message) hw
    (by
      apply div_le_div_of_nonneg_right _ hN.le
      have : ((entries parameter cache leafIndex).ncard : ℝ) + remaining ≤ q := by
        exact_mod_cast hremaining
      linarith)
  refine hrace.trans ?_
  unfold leafPotential
  apply add_le_add le_rfl
  exact Finset.single_le_sum (f := fun message : Message => msgTerm realD realβ realP ((q : ℝ) + 1)
      ((cachedRandomizersAt parameter leafIndex message cache).card)
      ((validRandomizers parameter cache leafIndex message).card))
    (fun message _ => h.msgTerm_nonneg _ _) (Finset.mem_univ message)

end XmssSecurity.TargetSum.Direct.Collision
