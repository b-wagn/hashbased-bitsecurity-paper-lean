import Xmss.Proof.TargetSum.Direct.SourceQueryProjection
import Xmss.Proof.TargetSum.Direct.DecidingSecondLaneAccepted
import Xmss.Proof.TargetSum.ExpectedQueryAccounting
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! Prefix encoding queries are paid for by direct encoding queries and actual signer hashes. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum.CappedExecution

open Seeded

theorem countedSource_query_selected_cost (publicKey : PublicKey) (secretKey : Generic.SecretKey)
    (selected : OracleWorld.Domain → Prop) [DecidablePred selected]
    (hhash : ∀ input, selected input → IsHashQuery input)
    (input : (OracleWorld + SigningSpec).Domain) (state : CountedSourceState) :
    expectedSimulatedQueryCount romImpl selected
        (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey input) state.counts.cache +
        (state.counts.signing : ℝ≥0∞) ≤
      (if Direct.IsDirectWorldQuery selected input then 1 else 0) +
        ∑' result, Pr[= result | (countedSourceImpl secretKey input).run state] *
          (result.2.counts.signing : ℝ≥0∞) := by
  have hcounter : (∑' result, Pr[= result | (countedSourceImpl secretKey input).run state] *
      (result.2.counts.signing : ℝ≥0∞)) =
      ∑' result, Pr[= result | (referencePhaseCountsImpl secretKey input).run state.counts] *
        (result.2.signing : ℝ≥0∞) := by
    rw [← countedSourceImpl_counts_projection, tsum_probOutput_map_mul]
    rfl
  rw [hcounter]
  cases input with
  | inl input =>
      have hquery : expectedSimulatedQueryCount romImpl selected
          (liftM (OracleWorld.query input)) state.counts.cache = if selected input then 1 else 0 := by
        change expectedSimulatedQueryCount romImpl selected
          (liftM (OracleWorld.query input) >>= pure) state.counts.cache = _
        simp only [expectedSimulatedQueryCount_query_bind, expectedSimulatedQueryCount_pure,
          mul_zero, tsum_zero, add_zero]
      simp only [cappedSourceUnloggedMappedAdversaryImpl, hquery, Direct.IsDirectWorldQuery,
        referencePhaseCountsImpl, phaseCountsImpl, StateT.run, tsum_probOutput_map_mul]
      rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (probFailure_of_liftM_PMF _), one_mul]
      split_ifs <;> exact le_rfl
  | inr request =>
      simp only [Direct.IsDirectWorldQuery, if_false, zero_add,
        referencePhaseCountsImpl, phaseCountsImpl, StateT.run, tsum_probOutput_map_mul,
        Nat.cast_add, mul_add, ENNReal.tsum_add]
      rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (probFailure_of_liftM_PMF _), one_mul]
      rw [add_comm]
      apply add_le_add le_rfl
      change expectedSimulatedQueryCount romImpl selected
        (Signing.precomputedCappedSign secretKey request.epoch request.message) state.counts.cache ≤
        ∑' result, Pr[= result | (simulateQ romImpl (countHashQueries
          (Signing.precomputedCappedSign secretKey request.epoch request.message))).run state.counts.cache] *
          (result.1.2 : ℝ≥0∞)
      apply (expectedSimulatedQueryCount_mono romImpl selected
        (fun input : OracleWorld.Domain => input matches .inr _) hhash _ _).trans_eq
      exact expectedSimulatedQueryCount_eq_counted romImpl
        (fun input : OracleWorld.Domain => input matches .inr _)
        (Signing.precomputedCappedSign secretKey request.epoch request.message) state.counts.cache

theorem countedSource_expected_selected_le {α : Type} (publicKey : PublicKey) (secretKey : Generic.SecretKey)
    (selected : OracleWorld.Domain → Prop) [DecidablePred selected]
    (hhash : ∀ input, selected input → IsHashQuery input)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec) :
    expectedSimulatedQueryCount romImpl selected
        (simulateQ (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey) computation) cache ≤
      expectedSimulatedQueryCount (cappedUnloggedMappedAdversaryImpl publicKey secretKey)
        (Direct.IsDirectWorldQuery selected) computation cache +
        ∑' result, Pr[= result | (simulateQ (countedSourceImpl secretKey) computation).run
          (CountedSourceState.initial cache)] * (result.2.counts.signing : ℝ≥0∞) := by
  have hproject input state :
      Prod.map id (fun state : CountedSourceState => state.counts.cache) <$>
        (countedSourceImpl secretKey input).run state =
          (simulateQ romImpl (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey input)).run
            state.counts.cache := by
    change (fun result => (result.1, result.2.counts.cache)) <$>
      (countedSourceImpl secretKey input).run state = _
    rw [countedSourceImpl_cache_projection publicKey secretKey]
    cases input with
    | inl input => simp only [cappedSourceUnloggedMappedAdversaryImpl, simulateQ_spec_query]; rfl
    | inr request => rfl
  have h := expectedSimulatedQueryCount_simulate_le_accounting
    (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey) romImpl (countedSourceImpl secretKey)
    (fun state => state.counts.cache) hproject selected (Direct.IsDirectWorldQuery selected)
    (fun state => (state.counts.signing : ℝ≥0∞))
    (countedSource_query_selected_cost publicKey secretKey selected hhash)
    computation (CountedSourceState.initial cache)
  simpa only [countedSource_expectedQuery_eq publicKey, CountedSourceState.initial,
    Nat.cast_zero, add_zero] using h

end Xmss.TargetSum.CappedExecution

namespace Xmss.TargetSum.Direct

theorem expectedEncodingQueries_adversaryPhase_le (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : Generic.SecretKey) (cache : QueryCache HashSpec) :
    expectedSimulatedQueryCount romImpl (CappedEncodingMonitor.IsEncodingHashQuery secretKey.parameter)
        (Deciding.adversaryPhase adversary publicKey secretKey) cache ≤
      expectedSimulatedQueryCount (cappedUnloggedMappedAdversaryImpl publicKey secretKey)
        (Direct.IsDirectEncodingQuery secretKey.parameter) (adversary.main publicKey) cache +
        ∑' result, Pr[= result | (simulateQ (CappedExecution.countedSourceImpl secretKey)
          (adversary.main publicKey)).run (CappedExecution.CountedSourceState.initial cache)] *
            (result.2.counts.signing : ℝ≥0∞) := by
  have hproject := QueryImpl.fst_map_run_withTraceAppend
    (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey) signingLogFragment (adversary.main publicKey)
  rw [cappedSourceUnloggedMappedAdversaryImpl_withTraceAppend_eq] at hproject
  have hcount := congrArg (fun computation => expectedSimulatedQueryCount romImpl
    (CappedEncodingMonitor.IsEncodingHashQuery secretKey.parameter) computation cache) hproject
  rw [expectedSimulatedQueryCount_map] at hcount
  unfold Deciding.adversaryPhase
  rw [hcount]
  have h := CappedExecution.countedSource_expected_selected_le publicKey secretKey
    (CappedEncodingMonitor.IsEncodingHashQuery secretKey.parameter)
    (fun input h => by cases input with
      | inl input => exact h.elim
      | inr input => simp only [IsHashQuery]) (adversary.main publicKey) cache
  convert h using 1
  congr 2
  funext input
  rcases input with (uniform | input) | request <;> rfl

theorem expectedPrefixEncodingQueries_le (adversary : Adversary) :
    Deciding.expectedPrefixEncodingQueries adversary ≤
      Direct.expectedDirectEncodingQueries adversary + expectedSourceSignerHashes adversary := by
  unfold Deciding.expectedPrefixEncodingQueries Direct.expectedDirectEncodingQueries expectedSourceSignerHashes
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro keyResult
  rw [← mul_add]
  exact mul_le_mul' le_rfl (expectedEncodingQueries_adversaryPhase_le adversary _ _ _)

/-- info: 'Xmss.TargetSum.Direct.expectedPrefixEncodingQueries_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms expectedPrefixEncodingQueries_le

end Xmss.TargetSum.Direct
