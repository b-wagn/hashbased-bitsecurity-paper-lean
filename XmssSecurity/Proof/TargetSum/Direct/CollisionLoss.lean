import XmssSecurity.Proof.TargetSum.Direct.CollisionPrehitBound
import XmssSecurity.Proof.TargetSum.Direct.CountedSourceBudget
import XmssSecurity.Proof.TargetSum.Direct.StructuralQueries

/-!
# The prehit loss in closed form

For an adversary making at most `q < 2^127` direct encoding queries, the prehit loss is at most
`(q + 2^86) / 2^256` per expected direct encoding query (`collisionRate_le`), hence at most
`prehitRate = (2^127 + 2^86) / 2^256`, a little over half of `2^-128`, for every such `q`.

The bound holds both for a syntactic bound on the direct encoding queries
(`winningEncodingPrehit_probability_le_prehitRate`) and for a bound on the direct hash queries of
every supported branch of the reference execution (`..._of_phaseBudget`), the form in which the
signer-counted budget is available.
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Direct

open Collision CollisionMath

theorem collisionRate_le (q : ℕ) (hq : q + 1 ≤ 2 ^ 127) :
    collisionRate q ≤ ((q + 2 ^ 86 : ℕ) : ℝ≥0∞) / ((2 ^ 256 : ℕ) : ℝ≥0∞) := by
  have hrate := rate_le (hyp q hq) rfl rfl rfl realP_ge
  have hq' : (q : ℝ) + 1 ≤ 2 ^ 127 := by exact_mod_cast hq
  have hreal : rate realN realD realM realβ realP ((q : ℝ) + 1) ≤ ((q : ℝ) + 2 ^ 86) / 2 ^ 256 := by
    refine hrate.trans ?_
    unfold realN realD
    rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
    nlinarith
  unfold collisionRate
  rw [ENNReal.ofReal_le_iff_le_toReal (by finiteness)]
  refine hreal.trans_eq ?_
  rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  push_cast
  ring

/-- The prehit loss per expected direct encoding query, for any `q < 2^127`. -/
noncomputable def prehitRate : ℝ≥0∞ :=
  ((2 ^ 127 + 2 ^ 86 : ℕ) : ℝ≥0∞) / ((2 ^ 256 : ℕ) : ℝ≥0∞)

theorem collisionRate_le_prehitRate (q : ℕ) (hq : q + 1 ≤ 2 ^ 127) :
    collisionRate q ≤ prehitRate :=
  (collisionRate_le q hq).trans (ENNReal.div_le_div (by exact_mod_cast (by omega)) le_rfl)

theorem prehitRate_le_digest_inverse : prehitRate ≤ ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ := by
  unfold prehitRate
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_div, ENNReal.toReal_inv, digestBits]

theorem winningEncodingPrehit_probability_le_prehitRate (adversary : Adversary) (q : ℕ)
    (hq : q + 1 ≤ 2 ^ 127) (hbound : IsEncodingQueryBound adversary q) :
    Pr[WinningEncodingPrehitOccurs | cappedDetailedGameWithEncodingTrace adversary] ≤
      prehitRate * expectedDirectEncodingQueries adversary :=
  (winningEncodingPrehit_probability_le_collision adversary q hq hbound).trans
    (mul_le_mul' (collisionRate_le_prehitRate q hq) le_rfl)

theorem isEncodingQueryBound_of_direct {adversary : Adversary} {D : ℕ}
    (hD : IsDirectQueryBound adversary D) : IsEncodingQueryBound adversary D :=
  fun publicKey => (hD publicKey).of_imp (isDirectHashQuery_of_encoding publicKey.parameter)

/-- The prehit loss of an adversary with at most `D < 2^127` direct hash queries. -/
theorem winningEncodingPrehit_probability_le_direct_collision (adversary : Adversary) (D : ℕ)
    (hD : IsDirectQueryBound adversary D) (hsmall : D + 1 ≤ 2 ^ 127) :
    Pr[WinningEncodingPrehitOccurs | cappedDetailedGameWithEncodingTrace adversary] ≤
      ((D + 2 ^ 86 : ℕ) : ℝ≥0∞) * D / ((2 ^ 256 : ℕ) : ℝ≥0∞) := by
  have hexpected : expectedDirectEncodingQueries adversary ≤ D :=
    le_trans le_self_add (expectedDirectEncodingQueries_add_structural_le adversary D hD)
  refine (winningEncodingPrehit_probability_le_collision adversary D hsmall
    (isEncodingQueryBound_of_direct hD)).trans ?_
  calc
    _ ≤ ((D + 2 ^ 86 : ℕ) : ℝ≥0∞) / ((2 ^ 256 : ℕ) : ℝ≥0∞) * D :=
      mul_le_mul' (collisionRate_le D hsmall) hexpected
    _ = _ := by rw [div_eq_mul_inv, div_eq_mul_inv, mul_right_comm]

/-! ### A budget on every branch of the reference execution -/

theorem referencePhaseCounts_direct_mono {α : Type} (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : Seeded.PhaseCounts)
    (result : α × Seeded.PhaseCounts)
    (hresult : result ∈ support
      ((simulateQ (Seeded.referencePhaseCountsImpl secretKey) computation).run state)) :
    state.direct ≤ result.2.direct := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact le_rfl
  | query_bind input next ih =>
      rw [run_simulateQ_query_bind, mem_support_bind_iff] at hresult
      obtain ⟨head, hhead, htail⟩ := hresult
      exact (CappedChain.phaseCountsImpl_counts_mono _ input state head hhead).1.trans
        (ih head.1 head.2 result htail)

/-- At most `remaining` further direct hash queries on every branch of the reference execution
from `cache`, counting from some starting count. -/
def PhaseBudget (secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) Forgery)
    (remaining : ℕ) (cache : QueryCache HashSpec) : Prop :=
  ∃ direct signing, ∀ result ∈ support ((simulateQ (Seeded.referencePhaseCountsImpl secretKey)
    computation).run ⟨cache, direct, signing⟩), result.2.direct ≤ direct + remaining

theorem referencePhaseCounts_step (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (state : QueryCache HashSpec × SigningCacheTrace)
    (direct signing : ℕ)
    (mid : (OracleWorld + SigningSpec).Range input × (QueryCache HashSpec × SigningCacheTrace))
    (hmid : mid ∈ support
      ((cappedCacheTracedMappedAdversaryImpl publicKey secretKey input).run state)) :
    ∃ counts : Seeded.PhaseCounts, (mid.1, counts) ∈ support
        ((Seeded.referencePhaseCountsImpl secretKey input).run ⟨state.1, direct, signing⟩) ∧
      counts.cache = mid.2.1 ∧
      direct + (if IsDirectEncodingQuery secretKey.parameter input then 1 else 0) ≤
        counts.direct := by
  have hbase := cappedCacheTracedMappedAdversaryImpl_query_base_support publicKey secretKey input
    state mid hmid
  rcases input with (uniformInput | hashInput) | request
  · refine ⟨⟨mid.2.1, direct + Seeded.queryCost (.inl uniformInput), signing⟩, ?_, rfl, ?_⟩
    · change _ ∈ support ((fun result => (result.1, (⟨result.2, direct +
        Seeded.queryCost (.inl uniformInput), signing⟩ : Seeded.PhaseCounts))) <$>
          (romImpl (.inl uniformInput)).run state.1)
      rw [support_map]
      exact ⟨(mid.1, mid.2.1), hbase, rfl⟩
    · simp [IsDirectEncodingQuery]
  · refine ⟨⟨mid.2.1, direct + Seeded.queryCost (.inr hashInput), signing⟩, ?_, rfl, ?_⟩
    · change _ ∈ support ((fun result => (result.1, (⟨result.2, direct +
        Seeded.queryCost (.inr hashInput), signing⟩ : Seeded.PhaseCounts))) <$>
          (romImpl (.inr hashInput)).run state.1)
      rw [support_map]
      exact ⟨(mid.1, mid.2.1), hbase, rfl⟩
    · split_ifs <;> simp [Seeded.queryCost]
  · change (mid.1, mid.2.1) ∈ support ((simulateQ romImpl (Concrete.precomputedCappedSign secretKey
      request.epoch request.message)).run state.1) at hbase
    rw [← countHashQueries_run_forget, support_map] at hbase
    obtain ⟨counted, hcounted, heq⟩ := hbase
    refine ⟨⟨counted.2, direct, signing + counted.1.2⟩, ?_, ?_, ?_⟩
    · change _ ∈ support ((fun result => (result.1.1, (⟨result.2, direct,
        signing + result.1.2⟩ : Seeded.PhaseCounts))) <$>
          (simulateQ romImpl (countHashQueries (Concrete.precomputedCappedSign secretKey
            request.epoch request.message))).run state.1)
      rw [support_map]
      refine ⟨counted, hcounted, ?_⟩
      simp only [Prod.mk.injEq] at heq
      exact Prod.ext heq.1 rfl
    · simp only [Prod.mk.injEq] at heq
      exact heq.2
    · simp [IsDirectEncodingQuery]

theorem phaseBudget_step (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) Forgery)
    (remaining : ℕ) (state : QueryCache HashSpec × SigningCacheTrace)
    (hbudget : PhaseBudget secretKey (query input >>= next) remaining state.1) :
    (IsDirectEncodingQuery secretKey.parameter input → 0 < remaining) ∧
      ∀ mid ∈ support ((cappedCacheTracedMappedAdversaryImpl publicKey secretKey input).run state),
        ∃ remaining' ≤ (if IsDirectEncodingQuery secretKey.parameter input then remaining - 1
          else remaining), PhaseBudget secretKey (next mid.1) remaining' mid.2.1 := by
  obtain ⟨direct, signing, hbound⟩ := hbudget
  have hrun := run_simulateQ_query_bind (Seeded.referencePhaseCountsImpl secretKey) input next
    ⟨state.1, direct, signing⟩
  -- every supported step leaves the remaining budget for the continuation
  have hafter : ∀ mid ∈ support ((cappedCacheTracedMappedAdversaryImpl publicKey secretKey
      input).run state), ∃ counts : Seeded.PhaseCounts, counts.cache = mid.2.1 ∧
        direct + (if IsDirectEncodingQuery secretKey.parameter input then 1 else 0) ≤
          counts.direct ∧ counts.direct ≤ direct + remaining ∧
        ∀ result ∈ support ((simulateQ (Seeded.referencePhaseCountsImpl secretKey)
          (next mid.1)).run counts), result.2.direct ≤ direct + remaining := by
    intro mid hmid
    obtain ⟨counts, hcounts, hcache, hdirect⟩ :=
      referencePhaseCounts_step publicKey secretKey input state direct signing mid hmid
    have hcont : ∀ result ∈ support ((simulateQ (Seeded.referencePhaseCountsImpl secretKey)
        (next mid.1)).run counts), result.2.direct ≤ direct + remaining := by
      intro result hresult
      apply hbound
      change result ∈ support ((simulateQ (Seeded.referencePhaseCountsImpl secretKey)
        (liftM ((OracleWorld + SigningSpec).query input) >>= next)).run _)
      rw [hrun, mem_support_bind_iff]
      exact ⟨(mid.1, counts), hcounts, hresult⟩
    obtain ⟨result, hresult⟩ := probComp_support_nonempty
      ((simulateQ (Seeded.referencePhaseCountsImpl secretKey) (next mid.1)).run counts)
    exact ⟨counts, hcache, hdirect,
      (referencePhaseCounts_direct_mono secretKey _ counts result hresult).trans
        (hcont result hresult), hcont⟩
  refine ⟨fun hP => ?_, fun mid hmid => ?_⟩
  · obtain ⟨mid, hmid⟩ := probComp_support_nonempty
      ((cappedCacheTracedMappedAdversaryImpl publicKey secretKey input).run state)
    obtain ⟨counts, -, hdirect, hle, -⟩ := hafter mid hmid
    rw [if_pos hP] at hdirect
    omega
  · obtain ⟨counts, hcache, hdirect, hle, hcont⟩ := hafter mid hmid
    refine ⟨remaining - (counts.direct - direct), ?_, counts.direct, counts.signing, ?_⟩
    · split_ifs at hdirect ⊢ <;> omega
    · intro result hresult
      have hstate : (⟨mid.2.1, counts.direct, counts.signing⟩ : Seeded.PhaseCounts) = counts := by
        rw [← hcache]
      rw [hstate] at hresult
      have := hcont result hresult
      omega

/-- The prehit loss when every branch of the reference execution makes at most `q < 2^127`
direct hash queries. -/
theorem winningEncodingPrehit_probability_le_prehitRate_of_phaseBudget (adversary : Adversary)
    (q : ℕ) (hq : q + 1 ≤ 2 ^ 127)
    (hbound : ∀ keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅),
      ∀ result ∈ support ((simulateQ (Seeded.referencePhaseCountsImpl keyResult.1.2)
        (adversary.main keyResult.1.1)).run ⟨keyResult.2, 0, 0⟩), result.2.direct ≤ q) :
    Pr[WinningEncodingPrehitOccurs | cappedDetailedGameWithEncodingTrace adversary] ≤
      prehitRate * expectedDirectEncodingQueries adversary :=
  (winningEncodingPrehit_probability_le_collision_of_budget adversary q hq
    (fun _ secretKey computation remaining state =>
      PhaseBudget secretKey computation remaining state.1)
    (fun keyResult _ input next remaining state hbudget =>
      phaseBudget_step keyResult.1.1 keyResult.1.2 input next remaining state hbudget)
    (fun keyResult hkeyResult => ⟨0, 0, fun result hresult => by
      simpa using hbound keyResult hkeyResult result hresult⟩)).trans
    (mul_le_mul' (collisionRate_le_prehitRate q hq) le_rfl)

end XmssSecurity.TargetSum.Direct
