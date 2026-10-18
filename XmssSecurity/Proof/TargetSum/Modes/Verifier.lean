import XmssSecurity.Proof.TargetSum.Modes.Keygen
import XmssSecurity.Proof.Generic.Direct.PruneSuccess
import XmssSecurity.Proof.TargetSum.ExactVerifierQueryCount
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Security when direct queries and verification are charged. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.TargetSum.Modes

theorem verifierQueryBound_eq : Generic.Direct.verifierQueryBound = 133 := by decide

open XmssSecurity.Modes

attribute [local irreducible] Generic.sampleMasterSeed

theorem gameCounted_verifier_eq (adversary : Generic.Security.StatementAdversary) :
    SUFCMA.gameCounted ⟨false, false, true, false⟩
        (RandomOracleModel.hashCost HashInput HashOutput) Generic.xmss adversary = (do
      let (publicKey, secretKey) ← Generic.xmss.keygen
      let ((forgery, charged), log) ← (simulateQ (Generic.Security.adversaryImpl secretKey)
        (QueryCounting.counted Generic.Direct.IsDirectHashQuery (adversary.main publicKey))).run
      let (verified, verifierCharged) ← Generic.countHashQueries
        (Generic.xmss.verify publicKey forgery.epoch forgery.message forgery.signature)
      pure (decide (Generic.SigningTranscript.Valid log ∧ ¬Generic.SigningTranscript.Contains log forgery) && verified,
        charged + verifierCharged)) := by
  unfold SUFCMA.gameCounted
  simp only [SUFCMA.costIf, Bool.false_eq_true, if_false, if_true,
    charge_zero, impl_direct_eq, bind_map_left, zero_add, charge_hashCost_eq_countHashQueries]
  apply bind_congr
  rintro ⟨publicKey, secretKey⟩
  rw [Generic.Security.run_withAddCost_eq_counted _ _ (fun input => by
    rcases input with (uniformOrHash | request)
    · rcases uniformOrHash with uniformInput | hashInput <;> rfl
    · rfl)]
  rfl

theorem adversary_counted_add_verification_bound
    (adversary : Generic.Security.StatementAdversary) (q : ℕ)
    (hbound : (SUFCMA.notion ⟨false, false, true, false⟩).HasQueryBound Generic.xmss adversary q)
    (publicKey : PublicKey) (secretKey : Generic.Seeded.SecretKey) (cache : QueryCache HashSpec)
    (hkeys : ((publicKey, secretKey), cache) ∈ support ((simulateQ Generic.romImpl Generic.xmss.keygen).run ∅))
    (forgery : Generic.Forgery) (charged : ℕ) (log : QueryLog Generic.SigningSpec) (cache' : QueryCache HashSpec)
    (hadversary : (((forgery, charged), log), cache') ∈ support ((simulateQ Generic.romImpl
      (simulateQ (Generic.Security.adversaryImpl secretKey)
        (QueryCounting.counted Generic.Direct.IsDirectHashQuery (adversary.main publicKey))).run).run cache))
    (verification : (Bool × ℕ) × QueryCache HashSpec)
    (hverification : verification ∈ support ((simulateQ Generic.romImpl (Generic.countHashQueries
      (Generic.xmss.verify publicKey forgery.epoch forgery.message forgery.signature))).run cache')) :
    charged + verification.1.2 ≤ q := by
  refine hbound (decide (Generic.SigningTranscript.Valid log ∧
    ¬Generic.SigningTranscript.Contains log forgery) && verification.1.1, charged + verification.1.2) ?_
  simp only [SUFCMA.notion, RandomOracleModel.run]
  rw [← Generic.Security.romImpl_eq, gameCounted_verifier_eq, StateT.run'_eq, support_map]
  refine ⟨((decide (Generic.SigningTranscript.Valid log ∧ ¬Generic.SigningTranscript.Contains log forgery) &&
    verification.1.1, charged + verification.1.2), verification.2), ?_, rfl⟩
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
  exact ⟨((publicKey, secretKey), cache), hkeys,
    (((forgery, charged), log), cache'), hadversary, verification, hverification, by simp⟩

theorem successful_adversary_counted_bound
    (adversary : Generic.Security.StatementAdversary) (q : ℕ)
    (hbound : (SUFCMA.notion ⟨false, false, true, false⟩).HasQueryBound Generic.xmss adversary q)
    (publicKey : PublicKey) (secretKey : Generic.Seeded.SecretKey) (cache : QueryCache HashSpec)
    (hkeys : ((publicKey, secretKey), cache) ∈ support ((simulateQ Generic.romImpl Generic.xmss.keygen).run ∅))
    (forgery : Generic.Forgery) (charged : ℕ) (log : QueryLog Generic.SigningSpec) (cache' : QueryCache HashSpec)
    (hadversary : (((forgery, charged), log), cache') ∈ support ((simulateQ Generic.romImpl
      (simulateQ (Generic.Security.adversaryImpl secretKey)
        (QueryCounting.counted Generic.Direct.IsDirectHashQuery (adversary.main publicKey))).run).run cache))
    (verification : Bool × QueryCache HashSpec)
    (hverification : verification ∈ support ((simulateQ Generic.romImpl
      (Generic.xmss.verify publicKey forgery.epoch forgery.message forgery.signature)).run cache'))
    (haccepts : verification.1 = true) : charged + Generic.Direct.verifierQueryBound ≤ q := by
  rw [← Generic.countHashQueries_run_forget _ cache', support_map] at hverification
  obtain ⟨countedVerification, hcounted, hproject⟩ := hverification
  have hverified : countedVerification.1.1 = true :=
    (congrArg Prod.fst hproject).trans haccepts
  have hcount := verify_queryCount_eq_of_accepts publicKey forgery.epoch forgery.message
    forgery.signature cache' countedVerification hcounted hverified
  rw [← hcount]
  exact adversary_counted_add_verification_bound adversary q hbound publicKey secretKey cache hkeys
    forgery charged log cache' hadversary countedVerification hcounted

noncomputable def verifierPayoff (publicKey : PublicKey)
    (result : (Generic.Forgery × QueryLog Generic.SigningSpec) × QueryCache HashSpec) : ℝ≥0∞ :=
  Pr[= true | (simulateQ Generic.romImpl (do
    let verified ← Generic.xmss.verify publicKey result.1.1.epoch result.1.1.message result.1.1.signature
    pure (decide (Generic.SigningTranscript.Valid result.1.2 ∧
      ¬Generic.SigningTranscript.Contains result.1.2 result.1.1) && verified))).run' result.2]

theorem verifierPayoff_eq_zero_of_over_budget
    (adversary : Generic.Security.StatementAdversary) (q : ℕ)
    (hbound : (SUFCMA.notion ⟨false, false, true, false⟩).HasQueryBound Generic.xmss adversary q)
    (publicKey : PublicKey) (secretKey : Generic.Seeded.SecretKey) (cache : QueryCache HashSpec)
    (hkeys : ((publicKey, secretKey), cache) ∈ support ((simulateQ Generic.romImpl Generic.xmss.keygen).run ∅))
    (forgery : Generic.Forgery) (charged : ℕ) (log : QueryLog Generic.SigningSpec) (cache' : QueryCache HashSpec)
    (hadversary : (((forgery, charged), log), cache') ∈ support ((simulateQ Generic.romImpl
      (simulateQ (Generic.Security.adversaryImpl secretKey)
        (QueryCounting.counted Generic.Direct.IsDirectHashQuery (adversary.main publicKey))).run).run cache))
    (hover : q < charged + Generic.Direct.verifierQueryBound) :
    verifierPayoff publicKey ((forgery, log), cache') = 0 := by
  unfold verifierPayoff
  rw [← probEvent_eq_eq_probOutput]
  apply probEvent_eq_zero
  intro result hresult htrue
  simp only [simulateQ_bind, StateT.run'_bind', mem_support_bind_iff] at hresult
  obtain ⟨verification, hverification, hfinal⟩ := hresult
  simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure,
    support_pure, Set.mem_singleton_iff] at hfinal
  rw [hfinal] at htrue
  simp only [Bool.and_eq_true] at htrue
  have haccepts : verification.1 = true := htrue.2
  have hle := successful_adversary_counted_bound adversary q hbound publicKey secretKey cache hkeys
    forgery charged log cache' hadversary verification hverification haccepts
  omega

theorem forgeAdvantage_le_prune_of_verifier_bound
    (adversary : Generic.Security.StatementAdversary) (q : ℕ)
    (hbound : (SUFCMA.notion ⟨false, false, true, false⟩).HasQueryBound Generic.xmss adversary q) :
    Generic.forgeAdvantage Generic.Seeded.scheme (Generic.Security.embed adversary) ≤
      Generic.forgeAdvantage Generic.Seeded.scheme
        (Generic.Direct.pruneAdversary (q - Generic.Direct.verifierQueryBound) (Generic.Security.embed adversary)) := by
  unfold Generic.forgeAdvantage Generic.gameCore
  simp only [simulateQ_bind, StateT.run'_bind', probOutput_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro keys
  by_cases hkeys : keys ∈ support ((simulateQ Generic.romImpl Generic.Seeded.scheme.keygen).run ∅)
  · apply mul_le_mul' le_rfl
    rcases keys with ⟨⟨publicKey, secretKey⟩, cache⟩
    dsimp only
    unfold Generic.Seeded.gameRest
    conv_lhs => rw [simulateQ_bind, StateT.run'_bind', probOutput_bind_eq_tsum]
    conv_rhs => rw [simulateQ_bind, StateT.run'_bind', probOutput_bind_eq_tsum]
    change (∑' result, Pr[= result | (simulateQ Generic.romImpl
        (simulateQ (Generic.Security.adversaryImpl secretKey) (adversary.main publicKey)).run).run cache] *
        verifierPayoff publicKey result) ≤
      ∑' result, Pr[= result | (simulateQ Generic.romImpl (simulateQ (Generic.Security.adversaryImpl secretKey)
        (Generic.Direct.pruneDirect (q - Generic.Direct.verifierQueryBound) (adversary.main publicKey))).run).run cache] *
        verifierPayoff publicKey result
    apply Generic.Direct.expected_logged_le_prune_of_zero_over_budget
    rintro ⟨⟨⟨forgery, charged⟩, log⟩, cache'⟩ hadversary hover
    exact verifierPayoff_eq_zero_of_over_budget adversary q hbound publicKey secretKey cache hkeys
      forgery charged log cache' hadversary (by dsimp only at hover; omega)
  · rw [probOutput_eq_zero_of_not_mem_support hkeys, zero_mul, zero_mul]

theorem forgeAdvantage_eq_zero_of_small_verifier_budget
    (adversary : Generic.Security.StatementAdversary) (q : ℕ)
    (hbound : (SUFCMA.notion ⟨false, false, true, false⟩).HasQueryBound Generic.xmss adversary q)
    (hsmall : q < Generic.Direct.verifierQueryBound) :
    Generic.forgeAdvantage Generic.Seeded.scheme (Generic.Security.embed adversary) = 0 := by
  unfold Generic.forgeAdvantage Generic.gameCore
  simp only [simulateQ_bind, StateT.run'_bind', probOutput_bind_eq_tsum]
  apply ENNReal.tsum_eq_zero.mpr
  intro keys
  by_cases hkeys : keys ∈ support ((simulateQ Generic.romImpl Generic.Seeded.scheme.keygen).run ∅)
  · apply mul_eq_zero.mpr
    right
    rcases keys with ⟨⟨publicKey, secretKey⟩, cache⟩
    dsimp only
    unfold Generic.Seeded.gameRest
    conv_lhs => rw [simulateQ_bind, StateT.run'_bind', probOutput_bind_eq_tsum]
    change (∑' result, Pr[= result | (simulateQ Generic.romImpl
      (simulateQ (Generic.Security.adversaryImpl secretKey) (adversary.main publicKey)).run).run cache] *
      verifierPayoff publicKey result) = 0
    rw [← Generic.Direct.run_logged_counted_forget _ (adversary.main publicKey) cache,
      tsum_probOutput_map_mul]
    apply ENNReal.tsum_eq_zero.mpr
    rintro ⟨⟨⟨forgery, charged⟩, log⟩, cache'⟩
    by_cases hadversary : (((forgery, charged), log), cache') ∈ support ((simulateQ Generic.romImpl
      (simulateQ (Generic.Security.adversaryImpl secretKey)
        (QueryCounting.counted Generic.Direct.IsDirectHashQuery (adversary.main publicKey))).run).run cache)
    · rw [verifierPayoff_eq_zero_of_over_budget adversary q hbound publicKey secretKey cache hkeys
        forgery charged log cache' hadversary (by omega), mul_zero]
    · rw [probOutput_eq_zero_of_not_mem_support hadversary, zero_mul]
  · rw [probOutput_eq_zero_of_not_mem_support hkeys, zero_mul]

/-- Charging verification as well as the adversary's direct queries gives 127-bit security. -/
theorem sufCmaVerifier_127 :
    (SUFCMA.notion ⟨false, false, true, false⟩).HasClassicalSecurityBits Generic.xmss 127 := by
  intro q _hq adversary hbound
  by_cases hlarge : 2 ^ 127 ≤ q
  · calc
      _ ≤ 1 := probEvent_le_one
      _ = ((2 ^ 127 : ℕ) : ℝ≥0∞) / ((2 ^ 127 : ℕ) : ℝ≥0∞) :=
        (ENNReal.div_self (by norm_num) (ENNReal.natCast_ne_top _)).symm
      _ ≤ _ := by gcongr
  · rw [advantage_eq_of_mode _ SUFCMA.CountingMode.direct,
      notion_direct_advantage_eq, Generic.Security.notionDirect_advantage_eq]
    by_cases hsmall : q < Generic.Direct.verifierQueryBound
    · rw [forgeAdvantage_eq_zero_of_small_verifier_budget adversary q hbound hsmall]
      exact zero_le
    · refine (forgeAdvantage_le_prune_of_verifier_bound adversary q hbound).trans
        ((Direct.seeded_forgeAdvantage_le_sharedDecidingLoss _ _
          (Generic.Direct.pruneAdversary_isDirectQueryBound _ (Generic.Security.embed adversary))
            (by have := verifierQueryBound_eq; omega)).trans
          (sharedDecidingLoss_le_127_of_gap _ q ?_ (by omega)))
      rw [verifierQueryBound_eq] at hsmall ⊢
      omega

end XmssSecurity.TargetSum.Modes
