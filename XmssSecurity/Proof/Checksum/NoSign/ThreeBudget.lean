import XmssSecurity.Proof.Checksum.NoSign.Signed
import XmssSecurity.Proof.Checksum.NoSign.SignedLane
import XmssSecurity.Proof.Checksum.NoSign.SignerBridge
import XmssSecurity.Proof.Checksum.Direct.SharedDecidingBudget
import XmssSecurity.Proof.Generic.Direct.DecidingFirstLaneBridge
import XmssSecurity.Proof.Checksum.Code
import XmssSecurity.Proof.Checksum.EncodingProbability
/-!
# The budget of one request

With the signer's hashes and the requests charged and a budget of `3`, the adversary either signs
once and makes no hash query, or makes at most three hash queries and never signs; which, it
decides before its first hash query. Its executions with a request are those of its hash-free
pruning, which the deciding lanes bound by `3 / 2^128` plus `40 / 2^128` times the probability
`σ` of signing; its executions without a request are bounded by the top collision and the hidden
sibling, at `(8 - 6 σ) / 2^128` on average since its expected hash queries are at most
`3 - 3 σ`. Altogether the advantage is at most `45 / 2^128` (`threeBudget_advantage_le`).
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.Checksum.NoSign

open Deciding

/-! ## The executions with a request -/

theorem signed_le_deciding_lanes (adversary : Generic.Adversary) :
    Pr[fun execution : Generic.GameOutcome × QueryCache HashSpec =>
        execution.1.won = true ∧ execution.1.signingLog ≠ [] |
      Generic.detailedGameWithCache Generic.Concrete.scheme adversary] ≤
      Pr[Generic.Deciding.WinningDecidingFirstLaneBadEventOccurs | Generic.cappedDetailedGameWithEncodingTrace adversary] +
        (Pr[Generic.WinningEncodingPrehitOccurs | Generic.cappedDetailedGameWithEncodingTrace adversary] +
          Pr[fun execution : Generic.GameOutcome × QueryCache HashSpec => execution.1.won = true ∧
            ¬ Generic.OutcomeBadEventOccurs execution.2 execution.1 .encoding ∧
            ¬ Generic.Deciding.DecidingChainValueRevealed execution.2 execution.1 ∧ execution.1.signingLog ≠ [] |
            Generic.detailedGameWithCache Generic.Concrete.scheme adversary]) := by
  rw [← Generic.cappedDetailedGameWithEncodingTrace_cache_projection, probEvent_map, probEvent_map]
  calc
    _ ≤ Pr[fun execution : Generic.CappedEncodingTraceExecution =>
          Generic.Deciding.WinningDecidingFirstLaneBadEventOccurs execution ∨
            (Generic.WinningEncodingPrehitOccurs execution ∨
              (execution.1.won = true ∧ ¬ Generic.OutcomeBadEventOccurs execution.2.1.1 execution.1 .encoding ∧
                ¬ Generic.Deciding.DecidingChainValueRevealed execution.2.1.1 execution.1 ∧
                execution.1.signingLog ≠ [])) |
          Generic.cappedDetailedGameWithEncodingTrace adversary] := by
      apply probEvent_mono
      intro execution _hmem hwin
      by_cases hprehit : Generic.WinningEncodingPrehitOccurs execution
      · exact Or.inr (Or.inl hprehit)
      by_cases hencoding : Generic.OutcomeBadEventOccurs execution.2.1.1 execution.1 .encoding
      · exact Or.inl (Or.inl ⟨⟨hwin.1, hencoding⟩, hprehit⟩)
      by_cases hrevealed : Generic.Deciding.DecidingChainValueRevealed execution.2.1.1 execution.1
      · exact Or.inl (Or.inr ⟨hwin.1, hrevealed⟩)
      · exact Or.inr (Or.inr ⟨hwin.1, hencoding, hrevealed, hwin.2⟩)
    _ ≤ _ := by
      apply (probEvent_or_le _ Generic.Deciding.WinningDecidingFirstLaneBadEventOccurs _).trans
      exact add_le_add le_rfl (probEvent_or_le _ Generic.WinningEncodingPrehitOccurs _)

/-- The adversary with every direct hash query answered by `default` without querying. -/
noncomputable def hashFree (adversary : Generic.Adversary) : Generic.Adversary :=
  ⟨fun publicKey => Generic.Direct.pruneDirect 0 (adversary.main publicKey)⟩

theorem probEvent_game_phases (adversary : Generic.Adversary)
    (event : Generic.GameOutcome × QueryCache HashSpec → Prop) :
    Pr[event | Generic.detailedGameWithCache Generic.Concrete.scheme adversary] =
      ∑' keyResult, Pr[= keyResult | (simulateQ Generic.romImpl Generic.Concrete.scheme.keygen).run ∅] *
        ∑' prefixResult, Pr[= prefixResult |
            realRun keyResult.1.2 (adversary.main keyResult.1.1) keyResult.2] *
          Pr[event | (simulateQ Generic.romImpl (Generic.Deciding.verificationPhase keyResult.1.1 keyResult.1.2
            prefixResult.1)).run prefixResult.2] := by
  unfold Generic.detailedGameWithCache Generic.detailedGameCore
  simp only [Generic.Deciding.detailedGameAfterKeygen_eq_phases]
  rw [simulateQ_bind, StateT.run_bind, probEvent_bind_eq_tsum]
  refine tsum_congr fun keyResult => congrArg _ ?_
  rw [simulateQ_bind, StateT.run_bind, probEvent_bind_eq_tsum]
  rfl

/-- When a request can only come first, the winning executions with a request are those of the
hash-free adversary. -/
theorem signed_won_eq_hashFree (adversary : Generic.Adversary)
    (hweighted : ∀ publicKey, IsWeightedBound 3 (adversary.main publicKey) 3) :
    Pr[fun execution : Generic.GameOutcome × QueryCache HashSpec =>
        execution.1.won = true ∧ execution.1.signingLog ≠ [] |
      Generic.detailedGameWithCache Generic.Concrete.scheme adversary] =
      Pr[fun execution : Generic.GameOutcome × QueryCache HashSpec =>
          execution.1.won = true ∧ execution.1.signingLog ≠ [] |
        Generic.detailedGameWithCache Generic.Concrete.scheme (hashFree adversary)] := by
  rw [probEvent_game_phases, probEvent_game_phases]
  refine tsum_congr fun keyResult => congrArg _ (tsum_congr fun prefixResult => ?_)
  by_cases hsigned : prefixResult.1.2 ≠ []
  · congr 1
    have h := probEvent_realRun_sign_eq keyResult.1.2 3 3 (adversary.main keyResult.1.1)
      (hweighted keyResult.1.1) le_rfl keyResult.2 (· = prefixResult)
    rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
    calc
      _ = Pr[fun result => result = prefixResult ∧ result.1.2 ≠ [] |
            realRun keyResult.1.2 (adversary.main keyResult.1.1) keyResult.2] :=
        probEvent_congr' (fun result _ => ⟨fun heq => ⟨heq, heq ▸ hsigned⟩, fun h => h.1⟩) rfl
      _ = _ := h
      _ = _ := probEvent_congr' (fun result _ => ⟨fun h => h.1, fun heq => ⟨heq, heq ▸ hsigned⟩⟩)
        rfl
  · have hzero : ∀ secretKey publicKey,
        Pr[fun execution : Generic.GameOutcome × QueryCache HashSpec =>
            execution.1.won = true ∧ execution.1.signingLog ≠ [] |
          (simulateQ Generic.romImpl (Generic.Deciding.verificationPhase publicKey secretKey prefixResult.1)).run
            prefixResult.2] = 0 := fun secretKey publicKey =>
      probEvent_eq_zero fun execution hexecution hevent => hsigned (by
        rw [← (Generic.Deciding.verificationPhase_support _ _ _ _ _ hexecution).2.2.2.1]
        exact hevent.2)
    simp only [hzero, mul_zero]

/-! ## The executions without a request -/

/-- A predicate at the top address never holds for an encoding input. -/
theorem not_top_encodingInput (parameter : PublicParameter) (leafIndex : LeafIndex)
    (payload : Message × Randomness) :
    ¬ Generic.AtHashAddress parameter (.merkle topLevel Generic.Concrete.rootNode)
      (Generic.Concrete.CacheView.encodingInput parameter leafIndex payload) := by
  simp [Generic.Concrete.CacheView.encodingInput]

/-- The top collision of one key-generation result, with the adversary's expected direct hash
queries. -/
theorem topFresh_keyResult_le (adversary : Generic.Adversary)
    (keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec)
    (hparam : keyResult.1.1.parameter = keyResult.1.2.parameter) :
    Pr[fun execution : Generic.GameOutcome × QueryCache HashSpec =>
        Generic.Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
          (topTarget keyResult.1.2 keyResult.2) |
      (simulateQ Generic.romImpl (Generic.Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2 >>=
        Generic.Deciding.verificationPhase keyResult.1.1 keyResult.1.2)).run keyResult.2] ≤
      (expectedSimulatedQueryCount (Generic.cappedUnloggedMappedAdversaryImpl keyResult.1.1 keyResult.1.2)
          Generic.Direct.IsDirectHashQuery (adversary.main keyResult.1.1) keyResult.2 + 1) *
        digestInverse := by
  classical
  refine (Generic.Rom.mixed_adaptiveFreshDigestCollisionWith_le_expected_moved _ _ _ _
    fun _ _ hcollision => hcollision).trans ?_
  rw [div_eq_mul_inv]
  refine mul_le_mul' ?_ le_rfl
  let atTop := Generic.Rom.IsRelevantHashQuery
    (Generic.AtHashAddress keyResult.1.2.parameter (.merkle topLevel Generic.Concrete.rootNode))
  calc
    _ ≤ expectedSimulatedQueryCount Generic.romImpl atTop
          (Generic.Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2 >>=
            Generic.Deciding.verificationPhase keyResult.1.1 keyResult.1.2) keyResult.2 := by
      refine expectedSimulatedQueryCount_mono Generic.romImpl _ _ (fun input hinput => ?_) _ _
      rcases input with _ | hashInput
      · exact hinput.elim
      · exact atTop_of_topTarget_ne keyResult.1.2 keyResult.2 hashInput hinput
    _ = expectedSimulatedQueryCount Generic.romImpl atTop
          (Generic.Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2) keyResult.2 +
        ∑' prefixResult, Pr[= prefixResult | (simulateQ Generic.romImpl
            (Generic.Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run keyResult.2] *
          expectedSimulatedQueryCount Generic.romImpl atTop
            (Generic.Deciding.verificationPhase keyResult.1.1 keyResult.1.2 prefixResult.1)
            prefixResult.2 :=
      expectedSimulatedQueryCount_bind Generic.romImpl _ _ _ _
    _ ≤ _ := by
      refine add_le_add ?_ ?_
      · rw [expectedQueries_adversaryPhase_eq _ keyResult.1.2
          (fun leafIndex payload => not_top_encodingInput _ leafIndex payload)]
        exact expectedDirectWorld_le_direct _ _ _ _
      · refine Generic.Direct.tsum_probOutput_mul_le _ _ _ fun prefixResult => ?_
        rw [Generic.Deciding.expectedQueries_verificationPhase_eq]
        have hbound := scheme_verify_top_one keyResult.1.1 prefixResult.1.1.epoch
          prefixResult.1.1.message prefixResult.1.1.signature
        rw [hparam] at hbound
        exact_mod_cast expectedSimulatedQueryCount_le_of_isQueryBoundP Generic.romImpl _ _ _ 1 hbound

/-- A winning execution without a request forges the hidden sibling or collides at the top. -/
theorem unsigned_keyResult_le (adversary : Generic.Adversary)
    (keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support ((simulateQ Generic.romImpl Generic.Concrete.scheme.keygen).run ∅)) :
    Pr[fun execution : Generic.GameOutcome × QueryCache HashSpec =>
        execution.1.won = true ∧ execution.1.signingLog = [] |
      (simulateQ Generic.romImpl (Generic.Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2 >>=
        Generic.Deciding.verificationPhase keyResult.1.1 keyResult.1.2)).run keyResult.2] ≤
      Pr[fun prefixResult : (Generic.Forgery × QueryLog Generic.SigningSpec) × QueryCache HashSpec =>
          HiddenSiblingGuessed keyResult.2 keyResult.1.2 prefixResult.1.1 ∧
            prefixResult.1.2 = [] |
        (simulateQ Generic.romImpl (Generic.Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2] +
      Pr[fun execution : Generic.GameOutcome × QueryCache HashSpec =>
          Generic.Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
            (topTarget keyResult.1.2 keyResult.2) |
        (simulateQ Generic.romImpl (Generic.Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2 >>=
          Generic.Deciding.verificationPhase keyResult.1.1 keyResult.1.2)).run keyResult.2] := by
  have hrest : (simulateQ Generic.romImpl (Generic.Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2 >>=
        Generic.Deciding.verificationPhase keyResult.1.1 keyResult.1.2)).run keyResult.2 =
      (simulateQ Generic.romImpl (Generic.Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2 >>= fun prefixResult =>
        (simulateQ Generic.romImpl (Generic.Deciding.verificationPhase keyResult.1.1 keyResult.1.2
          prefixResult.1)).run prefixResult.2 := by
    simp only [simulateQ_bind, StateT.run_bind]
  calc
    _ ≤ Pr[fun execution : Generic.GameOutcome × QueryCache HashSpec =>
          (HiddenSiblingGuessed keyResult.2 keyResult.1.2 execution.1.forgery ∧
            execution.1.signingLog = []) ∨
          Generic.Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
            (topTarget keyResult.1.2 keyResult.2) |
        (simulateQ Generic.romImpl (Generic.Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2 >>=
          Generic.Deciding.verificationPhase keyResult.1.1 keyResult.1.2)).run keyResult.2] := by
      refine probEvent_mono fun execution hexecution hwin => ?_
      rw [hrest, mem_support_bind_iff] at hexecution
      obtain ⟨prefixResult, hprefix, hafter⟩ := hexecution
      have hforgery := (Generic.Deciding.verificationPhase_support _ _ _ _ _ hafter).2.2.1
      rcases topCases adversary keyResult hkeygen prefixResult hprefix execution hafter hwin.1 with
        hguess | hfresh
      · exact Or.inl ⟨hforgery ▸ hguess, hwin.2⟩
      · exact Or.inr hfresh
    _ ≤ _ := by
      refine (probEvent_or_le _ _ _).trans (add_le_add ?_ le_rfl)
      rw [hrest]
      refine probEvent_bind_le_of_imp _ _ _ _ fun prefixResult _ execution hafter hguess => ?_
      have hsupport := Generic.Deciding.verificationPhase_support _ _ _ _ _ hafter
      rw [hsupport.2.2.1, hsupport.2.2.2.1] at hguess
      exact hguess

/-! ## The advantage -/

/-- The expected number of requests in the forwarded run. -/
noncomputable def signRate (adversary : Generic.Adversary) (publicKey : PublicKey) : ℝ≥0∞ :=
  expectedSimulatedQueryCount idealImpl IsSignQuery (adversary.main publicKey) ∅

theorem probEvent_signed_le_signRate (adversary : Generic.Adversary)
    (hweighted : ∀ publicKey, IsWeightedBound 3 (adversary.main publicKey) 3)
    (keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec) :
    Pr[fun prefixResult : (Generic.Forgery × QueryLog Generic.SigningSpec) × QueryCache HashSpec =>
        prefixResult.1.2 ≠ [] |
      (simulateQ Generic.romImpl (Generic.Deciding.adversaryPhase (Generic.Direct.withForgedEncodingQuery (hashFree adversary))
        keyResult.1.1 keyResult.1.2)).run keyResult.2] ≤ signRate adversary keyResult.1.1 := by
  let mapped := Generic.cappedUnloggedMappedAdversaryImpl keyResult.1.1 keyResult.1.2
  refine (probEvent_signingLog_ne_nil_le keyResult.1.1 keyResult.1.2 _ keyResult.2).trans
    (le_of_eq ?_)
  have htail : ∀ forgery : Generic.Forgery,
      (liftM ((OracleWorld + Generic.SigningSpec).query (.inl (.inr
          (Generic.Concrete.CacheView.encodingInput keyResult.1.1.parameter forgery.epoch
            (forgery.message, forgery.signature.randomness))))) >>= fun _ =>
        (pure forgery : OracleComp (OracleWorld + Generic.SigningSpec) Generic.Forgery)).IsQueryBoundP
        IsSignQuery 0 := fun forgery => by
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [IsSignQuery]), fun _ => trivial⟩
  calc
    expectedSimulatedQueryCount mapped IsSignQuery
        ((Generic.Direct.withForgedEncodingQuery (hashFree adversary)).main keyResult.1.1) keyResult.2 =
      expectedSimulatedQueryCount mapped IsSignQuery
        ((hashFree adversary).main keyResult.1.1) keyResult.2 := by
      change expectedSimulatedQueryCount mapped IsSignQuery
        ((hashFree adversary).main keyResult.1.1 >>= fun forgery =>
          liftM ((OracleWorld + Generic.SigningSpec).query (.inl (.inr
            (Generic.Concrete.CacheView.encodingInput keyResult.1.1.parameter forgery.epoch
              (forgery.message, forgery.signature.randomness))))) >>= fun _ =>
            (pure forgery : OracleComp (OracleWorld + Generic.SigningSpec) Generic.Forgery)) keyResult.2 = _
      rw [expectedSimulatedQueryCount_bind]
      simp only [expectedSign_eq_zero _ _ (htail _), mul_zero, tsum_zero, add_zero]
    _ = expectedSimulatedQueryCount mapped IsSignQuery (adversary.main keyResult.1.1)
          keyResult.2 :=
      expectedSign_pruneDirect_zero_eq mapped 3 3 _ (hweighted _) le_rfl (by norm_num) _
    _ = signRate adversary keyResult.1.1 :=
      expectedSign_eq_of_uniformFaithful mapped idealImpl
        (mappedImpl_uniformFaithful keyResult.1.1 keyResult.1.2) idealImpl_uniformFaithful 3 3
        _ (hweighted _) le_rfl (by norm_num) _ _

/-- With the signer's hashes and the requests charged and a budget of `3`, the concrete
advantage is at most `45 / 2^128`. -/
theorem threeBudget_advantage_le (adversary : Generic.Adversary)
    (hweighted : ∀ publicKey, IsWeightedBound 3 (adversary.main publicKey) 3) :
    Generic.forgeAdvantage Generic.Concrete.scheme adversary ≤ 45 * digestInverse := by
  classical
  let keygenRun := (simulateQ Generic.romImpl Generic.Concrete.scheme.keygen).run ∅
  let queried := Generic.Direct.withForgedEncodingQuery (hashFree adversary)
  have hfree : Generic.Direct.IsDirectQueryBound (hashFree adversary) 0 := fun publicKey =>
    Generic.Direct.pruneDirect_isQueryBoundP 0 _
  have hqueried := Generic.Direct.withForgedEncodingQuery_isDirectQueryBound _ 0 hfree
  have hdigest : ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ = digestInverse := rfl
  -- The executions with a request.
  have hsigned : Pr[fun execution : Generic.GameOutcome × QueryCache HashSpec =>
        execution.1.won = true ∧ execution.1.signingLog ≠ [] |
      Generic.detailedGameWithCache Generic.Concrete.scheme adversary] ≤
      3 * digestInverse + 40 * digestInverse *
        ∑' keyResult, Pr[= keyResult | keygenRun] * signRate adversary keyResult.1.1 := by
    rw [signed_won_eq_hashFree adversary hweighted,
      ← Generic.Direct.detailedGameWithCache_withForgedEncodingQuery]
    refine (signed_le_deciding_lanes queried).trans ?_
    have hfirst := Generic.Deciding.decidingFirstLane_withForgedEncodingQuery_probability_le (hashFree adversary) 0
      hfree
    have hprehit := Generic.Direct.winningEncodingPrehit_probability_le_expected_direct_encoding queried
    have hsecond := decidingSecondLane_signed_probability_le_expected queried (by
      intro keyResult hkeygen prefixResult hprefix
      have hparameter := Generic.Deciding.keygen_publicKey_parameter_eq keyResult hkeygen
      rw [← hparameter]
      exact Generic.Direct.adversaryPhase_withForgedEncodingQuery_cached (hashFree adversary)
        keyResult.1.1 keyResult.1.2 keyResult.2 prefixResult hprefix)
    have hcounts := Generic.Direct.expectedDirectEncodingQueries_add_structural_le queried 1 hqueried
    have hrate := Direct.encodingPrehitRate_le_digest_inverse
    have hsignedProb : signedProbability queried ≤
        ∑' keyResult, Pr[= keyResult | keygenRun] * signRate adversary keyResult.1.1 :=
      ENNReal.tsum_le_tsum fun keyResult => mul_le_mul' le_rfl
        (probEvent_signed_le_signRate adversary hweighted keyResult)
    calc
      _ ≤ ((0 + 2 : ℕ) : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
          (Generic.Direct.encodingPrehitRate * Generic.Direct.expectedDirectEncodingQueries queried +
            (Generic.Direct.expectedDirectStructuralQueries queried / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
              (40 : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) * signedProbability queried)) :=
        add_le_add hfirst (add_le_add hprehit hsecond)
      _ ≤ 2 * digestInverse + (digestInverse * Generic.Direct.expectedDirectEncodingQueries queried +
            (digestInverse * Generic.Direct.expectedDirectStructuralQueries queried +
              40 * digestInverse * ∑' keyResult, Pr[= keyResult | keygenRun] *
                signRate adversary keyResult.1.1)) := by
        refine add_le_add (le_of_eq ?_) (add_le_add ?_ (add_le_add (le_of_eq ?_) ?_))
        · rw [div_eq_mul_inv, hdigest]
          norm_num
        · exact mul_le_mul' (by rw [← hdigest]; exact hrate) le_rfl
        · rw [div_eq_mul_inv, hdigest, mul_comm]
        · rw [div_eq_mul_inv, hdigest]
          exact mul_le_mul' le_rfl hsignedProb
      _ = 2 * digestInverse + (digestInverse *
            (Generic.Direct.expectedDirectEncodingQueries queried +
              Generic.Direct.expectedDirectStructuralQueries queried) +
          40 * digestInverse * ∑' keyResult, Pr[= keyResult | keygenRun] *
            signRate adversary keyResult.1.1) := by ring
      _ ≤ 2 * digestInverse + (digestInverse * 1 +
          40 * digestInverse * ∑' keyResult, Pr[= keyResult | keygenRun] *
            signRate adversary keyResult.1.1) := by
        gcongr
        exact_mod_cast hcounts
      _ = _ := by ring
  -- The executions without a request.
  have hunsigned : Pr[fun execution : Generic.GameOutcome × QueryCache HashSpec =>
        execution.1.won = true ∧ execution.1.signingLog = [] |
      Generic.detailedGameWithCache Generic.Concrete.scheme adversary] ≤
      digestInverse * ∑' keyResult, Pr[= keyResult | keygenRun] *
        ((1 + idealSize adversary keyResult.1.1) +
          (expectedSimulatedQueryCount
            (Generic.cappedUnloggedMappedAdversaryImpl keyResult.1.1 keyResult.1.2)
            Generic.Direct.IsDirectHashQuery (adversary.main keyResult.1.1) keyResult.2 + 1)) := by
    unfold Generic.detailedGameWithCache Generic.detailedGameCore
    simp only [Generic.Deciding.detailedGameAfterKeygen_eq_phases]
    rw [simulateQ_bind, StateT.run_bind, probEvent_bind_eq_tsum]
    calc
      _ ≤ ∑' keyResult, Pr[= keyResult | keygenRun] *
            (Pr[fun prefixResult : (Generic.Forgery × QueryLog Generic.SigningSpec) × QueryCache HashSpec =>
                HiddenSiblingGuessed keyResult.2 keyResult.1.2 prefixResult.1.1 ∧
                  prefixResult.1.2 = [] |
              (simulateQ Generic.romImpl (Generic.Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run
                keyResult.2] +
            (expectedSimulatedQueryCount
                (Generic.cappedUnloggedMappedAdversaryImpl keyResult.1.1 keyResult.1.2)
                Generic.Direct.IsDirectHashQuery (adversary.main keyResult.1.1) keyResult.2 + 1) *
              digestInverse) := by
        refine ENNReal.tsum_le_tsum fun keyResult => ?_
        by_cases hkeygen : keyResult ∈ support keygenRun
        swap
        · rw [probOutput_eq_zero_of_not_mem_support hkeygen, zero_mul, zero_mul]
        exact mul_le_mul' le_rfl ((unsigned_keyResult_le adversary keyResult hkeygen).trans
          (add_le_add le_rfl (topFresh_keyResult_le adversary keyResult
            (Generic.Deciding.keygen_publicKey_parameter_eq keyResult hkeygen))))
      _ = (∑' keyResult, Pr[= keyResult | keygenRun] *
            Pr[fun prefixResult : (Generic.Forgery × QueryLog Generic.SigningSpec) × QueryCache HashSpec =>
                HiddenSiblingGuessed keyResult.2 keyResult.1.2 prefixResult.1.1 ∧
                  prefixResult.1.2 = [] |
              (simulateQ Generic.romImpl (Generic.Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run
                keyResult.2]) +
          digestInverse * ∑' keyResult, Pr[= keyResult | keygenRun] *
            (expectedSimulatedQueryCount
              (Generic.cappedUnloggedMappedAdversaryImpl keyResult.1.1 keyResult.1.2)
              Generic.Direct.IsDirectHashQuery (adversary.main keyResult.1.1) keyResult.2 + 1) := by
        rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
        exact tsum_congr fun keyResult => by ring
      _ ≤ digestInverse * (∑' keyResult, Pr[= keyResult | keygenRun] *
            (1 + idealSize adversary keyResult.1.1)) +
          digestInverse * ∑' keyResult, Pr[= keyResult | keygenRun] *
            (expectedSimulatedQueryCount
              (Generic.cappedUnloggedMappedAdversaryImpl keyResult.1.1 keyResult.1.2)
              Generic.Direct.IsDirectHashQuery (adversary.main keyResult.1.1) keyResult.2 + 1) := by
        refine add_le_add ?_ le_rfl
        rw [tsum_scheme_keygen_publicKey (fun publicKey => 1 + idealSize adversary publicKey)]
        exact hiddenSibling_unsigned_le adversary
      _ = _ := by
        rw [← mul_add, ← ENNReal.tsum_add]
        congr 1
        exact tsum_congr fun keyResult => by ring
  -- The two parts together.
  have hpointwise : ∀ keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec,
      40 * signRate adversary keyResult.1.1 +
          ((1 + idealSize adversary keyResult.1.1) +
            (expectedSimulatedQueryCount
              (Generic.cappedUnloggedMappedAdversaryImpl keyResult.1.1 keyResult.1.2)
              Generic.Direct.IsDirectHashQuery (adversary.main keyResult.1.1) keyResult.2 + 1)) ≤ 42 := by
    intro keyResult
    let σ := signRate adversary keyResult.1.1
    have hideal : idealSize adversary keyResult.1.1 + 3 * σ ≤ 3 := by
      refine (add_le_add (idealSize_le adversary keyResult.1.1) le_rfl).trans ?_
      unfold forwardPhase
      rw [expectedWorldHash_forwardOnly_eq]
      exact_mod_cast expected_direct_add_sign_le idealImpl 3 3 (adversary.main keyResult.1.1)
        (hweighted keyResult.1.1) ∅
    have hdirect : expectedSimulatedQueryCount
          (Generic.cappedUnloggedMappedAdversaryImpl keyResult.1.1 keyResult.1.2)
          Generic.Direct.IsDirectHashQuery (adversary.main keyResult.1.1) keyResult.2 + 3 * σ ≤ 3 := by
      have h := expected_direct_add_sign_le
        (Generic.cappedUnloggedMappedAdversaryImpl keyResult.1.1 keyResult.1.2) 3 3
        (adversary.main keyResult.1.1) (hweighted keyResult.1.1) keyResult.2
      rw [expectedSign_eq_of_uniformFaithful _ idealImpl
        (mappedImpl_uniformFaithful keyResult.1.1 keyResult.1.2) idealImpl_uniformFaithful 3 3
        (adversary.main keyResult.1.1) (hweighted keyResult.1.1) le_rfl (by norm_num) _ ∅] at h
      exact_mod_cast h
    have hσ : σ ≤ 1 := by
      have h := expected_direct_add_sign_le idealImpl 3 3 (adversary.main keyResult.1.1)
        (hweighted keyResult.1.1) ∅
      have h3 : (3 : ℝ≥0∞) * σ ≤ 3 * 1 := by
        rw [mul_one]
        exact le_trans le_add_self (by exact_mod_cast h)
      exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp h3
    calc
      _ = 34 * σ + (idealSize adversary keyResult.1.1 + 3 * σ) +
            (expectedSimulatedQueryCount
              (Generic.cappedUnloggedMappedAdversaryImpl keyResult.1.1 keyResult.1.2)
              Generic.Direct.IsDirectHashQuery (adversary.main keyResult.1.1) keyResult.2 + 3 * σ) + 2 := by
        ring
      _ ≤ 34 * 1 + 3 + 3 + 2 := by gcongr
      _ = 42 := by norm_num
  rw [Generic.forgeAdvantage_eq_detailedGameWithCache]
  calc
    _ ≤ Pr[fun execution : Generic.GameOutcome × QueryCache HashSpec =>
          execution.1.won = true ∧ execution.1.signingLog ≠ [] |
        Generic.detailedGameWithCache Generic.Concrete.scheme adversary] +
        Pr[fun execution : Generic.GameOutcome × QueryCache HashSpec =>
          execution.1.won = true ∧ execution.1.signingLog = [] |
        Generic.detailedGameWithCache Generic.Concrete.scheme adversary] := by
      refine (probEvent_mono fun execution _ hwin => ?_).trans (probEvent_or_le _ _ _)
      by_cases hlog : execution.1.signingLog = []
      · exact Or.inr ⟨hwin, hlog⟩
      · exact Or.inl ⟨hwin, hlog⟩
    _ ≤ 3 * digestInverse + digestInverse * ∑' keyResult, Pr[= keyResult | keygenRun] *
          (40 * signRate adversary keyResult.1.1 +
            ((1 + idealSize adversary keyResult.1.1) +
              (expectedSimulatedQueryCount
                (Generic.cappedUnloggedMappedAdversaryImpl keyResult.1.1 keyResult.1.2)
                Generic.Direct.IsDirectHashQuery (adversary.main keyResult.1.1) keyResult.2 + 1))) := by
      refine (add_le_add hsigned hunsigned).trans (le_of_eq ?_)
      have hsplit : ∀ (first second : (PublicKey × Generic.SecretKey) × QueryCache HashSpec → ℝ≥0∞),
          ∑' keyResult, Pr[= keyResult | keygenRun] * (40 * first keyResult + second keyResult) =
            40 * (∑' keyResult, Pr[= keyResult | keygenRun] * first keyResult) +
              ∑' keyResult, Pr[= keyResult | keygenRun] * second keyResult := by
        intro first second
        rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
        exact tsum_congr fun keyResult => by ring
      rw [hsplit]
      ring
    _ ≤ 3 * digestInverse + digestInverse * 42 :=
      add_le_add le_rfl (mul_le_mul' le_rfl
        (Generic.Direct.tsum_probOutput_mul_le _ _ _ hpointwise))
    _ = 45 * digestInverse := by ring

/-- With the signer's hashes and the requests charged, a budget of `3` gives advantage at most
`45 / 2^128 + 3 / 2^256`. -/
theorem signerRequests_three_advantage_le (adversary : Generic.Security.StatementAdversary)
    (hbound : (SUFCMA.notion ⟨false, true, false, true⟩).HasQueryBound Generic.xmss adversary 3) :
    (SUFCMA.notion ⟨false, true, false, true⟩).advantage Generic.xmss adversary ≤
      45 * digestInverse + (3 : ℕ) / ((2 ^ 256 : ℕ) : ℝ≥0∞) := by
  rw [Modes.advantage_eq_of_mode _ SUFCMA.CountingMode.direct,
    Modes.notion_direct_advantage_eq, Generic.Security.notionDirect_advantage_eq,
    forgeAdvantage_pruneWeighted_eq adversary true 3 hbound]
  let pruned : Generic.Adversary := ⟨fun publicKey =>
    pruneWeighted ((if true then 1 else 0) + 2) 3 (adversary.main publicKey)⟩
  have hdirect : Generic.Direct.IsDirectQueryBound pruned 3 := fun publicKey =>
    pruneWeighted_isQueryBoundP_direct _ 3 _
  refine (Generic.Seeded.forgeAdvantage_deterministic_le_reference_direct pruned 3 hdirect).trans ?_
  refine add_le_add (threeBudget_advantage_le _ fun publicKey => ?_) le_rfl
  exact memoize_isWeightedBound 3 3 _ ∅ (pruneWeighted_isWeightedBound _ _ _)

/-- info: 'XmssSecurity.Checksum.NoSign.signerRequests_three_advantage_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signerRequests_three_advantage_le

end XmssSecurity.Checksum.NoSign
