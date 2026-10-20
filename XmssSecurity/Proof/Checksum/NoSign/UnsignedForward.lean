import XmssSecurity.Proof.Checksum.NoSign.GuardedHiddenSibling

/-! Forwarding keeps an explicit count of signing requests, so the unsigned branch remains
visible after replacing the real signer by the refusing oracle. -/

open OracleComp OracleSpec ENNReal
open XmssSecurity.Generic

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.Checksum.NoSign

noncomputable def forwardMarked (computation : OracleComp (OracleWorld + SigningSpec) α) :
    OracleComp OracleWorld (α × ℕ) :=
  simulateQ forwardOnly (QueryCounting.counted IsSignQuery computation)

theorem forwardMarked_world_bind {α : Type} (world : OracleWorld.Domain)
    (next : OracleWorld.Range world → OracleComp (OracleWorld + SigningSpec) α) :
    forwardMarked (liftM ((OracleWorld + SigningSpec).query (.inl world)) >>= next) =
      (liftM (OracleWorld.query world) >>= fun answer => forwardMarked (next answer)) := by
  unfold forwardMarked
  rw [QueryCounting.counted_query_bind]
  simp only [IsSignQuery, if_false, zero_add, Prod.eta, bind_pure]
  rw [simulateQ_query_bind]
  rfl

theorem probEvent_realRun_noSign_le_marked {α : Type} (secretKey : Generic.SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec)
    (event : α × QueryCache HashSpec → Prop) :
    Pr[fun result => event (result.1.1, result.2) ∧ result.1.2 = [] |
      realRun secretKey computation cache] ≤
      Pr[fun result => event (result.1.1, result.2) ∧ result.1.2 = 0 |
        (simulateQ romImpl (forwardMarked computation)).run cache] := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value =>
      classical
      simp only [realRun, forwardMarked, QueryCounting.counted_pure, simulateQ_pure,
        WriterT.run_pure, StateT.run_pure, probEvent_pure]
      split_ifs <;> simp_all
  | query_bind input next ih =>
      unfold realRun
      rw [Direct.run_logged_query_bind]
      rcases input with world | request
      · rw [forwardMarked_world_bind, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
        rw [show (forwardOracles + signingOracle Concrete.scheme secretKey) (.inl world) =
            forwardOracles world from rfl, romImpl_forwardOracles_run, probEvent_bind_eq_tsum,
          tsum_probOutput_map_mul, probEvent_bind_eq_tsum]
        apply ENNReal.tsum_le_tsum
        intro result
        apply mul_le_mul' le_rfl
        rw [probEvent_map]
        simpa only [Function.comp_def, List.nil_append] using ih result.1 result.2
      · rw [probEvent_eq_zero fun outcome houtcome hevent => ?_]
        · exact zero_le
        rw [mem_support_bind_iff] at houtcome
        obtain ⟨step, hstep, hrest⟩ := houtcome
        rw [support_map] at hrest
        obtain ⟨rest, _, rfl⟩ := hrest
        exact signingOracle_run_log secretKey request cache step hstep
          (List.append_eq_nil_iff.mp hevent.2).1

theorem forwardMarked_projection (computation : OracleComp (OracleWorld + SigningSpec) α) :
    Prod.fst <$> forwardMarked computation = simulateQ forwardOnly computation := by
  rw [forwardMarked, ← simulateQ_map, QueryCounting.counted_forget]

theorem forwardMarked_sign_bind {α : Type} (request : SignRequest)
    (next : Option Generic.Signature → OracleComp (OracleWorld + SigningSpec) α) :
    forwardMarked (liftM ((OracleWorld + SigningSpec).query (.inr request)) >>= next) =
      (fun result => (result.1, 1 + result.2)) <$> forwardMarked (next none) := by
  unfold forwardMarked
  rw [QueryCounting.counted_query_bind, simulateQ_query_bind]
  change (pure none >>= fun answer => simulateQ forwardOnly
    (QueryCounting.counted IsSignQuery (next answer) >>= fun result =>
      pure (result.1, 1 + result.2))) = _
  rw [pure_bind, simulateQ_bind]
  simp only [simulateQ_pure, bind_pure_comp]

/-- At most one signing request makes the unsigned probability complementary to its expected
count. The inequality form also applies to subprobability implementations. -/
theorem marked_unsigned_add_sign_le {α : Type} (signCost budget : ℕ)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (h : IsWeightedBound signCost computation budget) (hbudget : budget ≤ signCost)
    (hpositive : 0 < signCost) (cache : QueryCache HashSpec) :
    Pr[fun result => result.1.2 = 0 |
        (simulateQ romImpl (forwardMarked computation)).run cache] +
      expectedSimulatedQueryCount idealImpl IsSignQuery computation cache ≤ 1 := by
  classical
  induction computation using OracleComp.inductionOn generalizing budget cache with
  | pure value =>
      simp only [forwardMarked, QueryCounting.counted_pure, simulateQ_pure,
        StateT.run_pure, probEvent_pure, expectedSimulatedQueryCount_pure]
      simp
  | query_bind input next ih =>
      rw [isWeightedBound_query_bind_iff] at h
      rcases input with world | request
      · rw [forwardMarked_world_bind, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
          probEvent_bind_eq_tsum, expectedSimulatedQueryCount_query_bind]
        have hstep : (idealImpl (.inl world)).run cache = (romImpl world).run cache := by
          simp only [idealImpl, forwardOnly, forwardWorld, QueryImpl.add_apply_inl,
            simulateQ_spec_query]
        rw [hstep]
        simp only [IsSignQuery, if_false, zero_add]
        change (∑' result : OracleWorld.Range world × QueryCache HashSpec,
          Pr[= result | (romImpl world).run cache] *
            Pr[fun outcome => outcome.1.2 = 0 |
              (simulateQ romImpl (forwardMarked (next result.1))).run result.2]) +
          (∑' result : OracleWorld.Range world × QueryCache HashSpec,
            Pr[= result | (romImpl world).run cache] *
              expectedSimulatedQueryCount idealImpl IsSignQuery (next result.1) result.2) ≤ 1
        rw [← ENNReal.tsum_add]
        apply (ENNReal.tsum_le_tsum fun result => ?_).trans
          (tsum_probOutput_le_one (mx := (romImpl world).run cache))
        rw [← mul_add]
        simpa using mul_le_mul' le_rfl
          (ih result.1 _ (h.2 result.1) (by omega) result.2)
      · rw [forwardMarked_sign_bind, simulateQ_map, StateT.run_map, probEvent_map]
        rw [probEvent_eq_zero (fun result _ hresult => by
          simp only [Function.comp_def] at hresult
          omega), zero_add, expectedSimulatedQueryCount_query_bind]
        simp only [IsSignQuery, if_true]
        have hnone : ∀ answer, (next answer).IsQueryBoundP IsSignQuery 0 := fun answer =>
          (h.2 answer).noSign (by simp only [actionWeight]; omega)
        simp only [expectedSign_eq_zero _ _ (hnone _), mul_zero, tsum_zero, add_zero, le_refl]

theorem idealProgramSize_forwardMarked (adversary : Adversary) (publicKey : PublicKey) :
    idealProgramSize (fun pk => forwardMarked (adversary.main pk)) publicKey =
      idealSize adversary publicKey := by
  have hproject : (fun result : (Forgery × ℕ) × QueryCache HashSpec =>
      (result.1.1, result.2)) <$>
      idealProgram (fun pk => forwardMarked (adversary.main pk)) publicKey =
      idealRun adversary publicKey := by
    have h := congrArg (fun body => (simulateQ romImpl body).run (∅ : QueryCache HashSpec))
      (forwardMarked_projection (adversary.main publicKey))
    simpa only [simulateQ_map, StateT.run_map, idealProgram, idealRun, forwardPhase] using h
  unfold idealProgramSize idealSize
  rw [← hproject, tsum_probOutput_map_mul]

noncomputable def unsignedRate (adversary : Adversary) (publicKey : PublicKey) : ℝ≥0∞ :=
  Pr[fun result => result.1.2 = 0 |
    idealProgram (fun pk => forwardMarked (adversary.main pk)) publicKey]

theorem hiddenSibling_unsigned_guard_le (adversary : Adversary) :
    ∑' keyResult, Pr[= keyResult | (simulateQ romImpl Concrete.scheme.keygen).run ∅] *
      Pr[fun prefixResult : (Forgery × QueryLog SigningSpec) × QueryCache HashSpec =>
          HiddenSiblingGuessed keyResult.2 keyResult.1.2 prefixResult.1.1 ∧
            prefixResult.1.2 = [] |
        (simulateQ romImpl (Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2] ≤
      digestInverse * publicKeyAverage fun publicKey =>
        unsignedRate adversary publicKey + idealSize adversary publicKey := by
  let body := fun pk => forwardMarked (adversary.main pk)
  have hdist : 𝒟[(simulateQ romImpl Concrete.scheme.keygen).run ∅] =
      𝒟[Concrete.materializeCachedKeyResult <$> (simulateQ romImpl Concrete.keygen).run ∅] := by
    rw [Concrete.evalDist_materialized_keygen_eq_precomputedKeygen]
    rfl
  calc
    _ ≤ ∑' keyResult, Pr[= keyResult | (simulateQ romImpl Concrete.scheme.keygen).run ∅] *
          Pr[fun result : (Forgery × ℕ) × QueryCache HashSpec =>
              HiddenSiblingGuessed keyResult.2 keyResult.1.2 result.1.1 ∧ result.1.2 = 0 |
            (simulateQ romImpl (body keyResult.1.1)).run keyResult.2] :=
      ENNReal.tsum_le_tsum fun keyResult => mul_le_mul' le_rfl
        (probEvent_realRun_noSign_le_marked keyResult.1.2 (adversary.main keyResult.1.1)
          keyResult.2 fun result => HiddenSiblingGuessed keyResult.2 keyResult.1.2 result.1)
    _ = ∑' keyResult, Pr[= keyResult | (simulateQ romImpl Concrete.keygen).run ∅] *
          Pr[fun result : (Forgery × ℕ) × QueryCache HashSpec =>
              HiddenSiblingGuessed keyResult.2 keyResult.1.2 result.1.1 ∧ result.1.2 = 0 |
            (simulateQ romImpl (body keyResult.1.1)).run keyResult.2] := by
      conv_lhs => arg 1; ext keyResult; arg 1; rw [probOutput_congr rfl hdist]
      rw [tsum_probOutput_map_mul]
      refine tsum_congr fun keyResult => ?_
      refine congrArg₂ (fun (p q : ℝ≥0∞) => p * q) rfl ?_
      simp only [Concrete.materializeCachedKeyResult_publicKey,
        Concrete.materializeCachedKeyResult_cache, Concrete.materializeCachedKeyResult_secretKey]
      apply probEvent_congr' _ rfl
      intro result _
      simp only [HiddenSiblingGuessed,
        Concrete.materializePrecomputation_parameter, Concrete.materializePrecomputation_chainStart]
    _ ≤ _ := by
      simpa only [idealProgramSize_forwardMarked, body, unsignedRate] using
        hiddenSibling_program_guard_le body Prod.fst (fun result => result.2 = 0)

end XmssSecurity.Checksum.NoSign
