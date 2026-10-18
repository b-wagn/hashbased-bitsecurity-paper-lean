import XmssSecurity.Proof.TargetSum.EUFCMA.FreshEncoding
import XmssSecurity.Proof.TargetSum.EncodingAcceptanceBudget
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.CacheDecode
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Accepted encodings of unrequested inputs are paid for by direct encoding
queries. Signing may remove such candidates but cannot create a new one. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.EUFCMA
open XmssSecurity.EUFCMA

open Concrete Generic.CappedChain

def HasFreshAcceptedEncoding (parameter : PublicParameter) (state : Generic.CappedChain.SourceTracedState) : Prop :=
  ∃ forgery : Generic.Forgery, ∃ output : Digest,
    ¬ SigningTranscript.ContainsRequest state.2.toSigningLog forgery ∧
    state.1 (Generic.Concrete.CacheView.encodingInput parameter forgery.epoch
      (forgery.message, forgery.signature.randomness)) = some output ∧
    Generic.Code.ValidDigest (output)

noncomputable instance (parameter : PublicParameter) : DecidablePred (HasFreshAcceptedEncoding parameter) :=
  Classical.decPred _

def IsDirectEncodingQuery (parameter : PublicParameter) : (OracleWorld + Generic.SigningSpec).Domain → Prop
  | .inl input => Generic.CappedEncodingMonitor.IsEncodingHashQuery parameter input
  | .inr _ => False

noncomputable instance (parameter : PublicParameter) : DecidablePred (IsDirectEncodingQuery parameter) :=
  Classical.decPred _

theorem hasFreshAcceptedEncoding_append_hash (parameter : PublicParameter)
    (cache : QueryCache HashSpec) (trace : Generic.AttackerActionTrace) (input : HashInput) :
    HasFreshAcceptedEncoding parameter (cache, trace ++ [.hash input]) ↔
      HasFreshAcceptedEncoding parameter (cache, trace) := by
  simp [HasFreshAcceptedEncoding, Generic.CappedChain.AttackerActionTrace.toSigningLog, Generic.CappedChain.AttackerAction.signingEntry?]

theorem hasFreshAcceptedEncoding_cacheQuery (parameter : PublicParameter)
    (cache : QueryCache HashSpec) (trace : Generic.AttackerActionTrace) (input : HashInput) (output : Digest)
    (hstate : ¬ HasFreshAcceptedEncoding parameter (cache, trace))
    (hnew : HasFreshAcceptedEncoding parameter (cache.cacheQuery input output, trace)) :
    (Generic.encodingInputLeafIndex? parameter input).isSome ∧ Generic.Code.ValidDigest (output) := by
  obtain ⟨forgery, answer, hfresh, hcache, hvalid⟩ := hnew
  dsimp only at hfresh hcache
  by_cases heq : Generic.Concrete.CacheView.encodingInput parameter forgery.epoch
      (forgery.message, forgery.signature.randomness) = input
  · rw [heq, QueryCache.cacheQuery_self] at hcache
    cases hcache
    exact ⟨by rw [← heq]; simp, hvalid⟩
  · rw [QueryCache.cacheQuery_of_ne _ _ heq] at hcache
    exact (hstate ⟨forgery, answer, hfresh, hcache, hvalid⟩).elim

theorem hasFreshAcceptedEncoding_signing (secretKey : Generic.SecretKey) (request : Generic.SignRequest)
    (cache finalCache : QueryCache HashSpec) (trace : Generic.AttackerActionTrace) (answer : Option Generic.Signature)
    (hsign : (answer, finalCache) ∈ support ((simulateQ Generic.romImpl
      (Generic.Concrete.precomputedCappedSign secretKey request.epoch request.message)).run cache))
    (hnew : HasFreshAcceptedEncoding secretKey.parameter (finalCache, trace ++ [.sign request answer])) :
    HasFreshAcceptedEncoding secretKey.parameter (cache, trace) := by
  obtain ⟨forgery, output, hfresh, hcache, hvalid⟩ := hnew
  dsimp only at hfresh hcache
  have hne : request ≠ forgery.request := by
    intro heq
    apply hfresh
    refine ⟨⟨request, answer⟩, ?_, heq⟩
    simp [Generic.CappedChain.AttackerActionTrace.toSigningLog, Generic.CappedChain.AttackerAction.signingEntry?]
  have holdFresh : ¬ SigningTranscript.ContainsRequest (Generic.CappedChain.AttackerActionTrace.toSigningLog trace) forgery := by
    rintro ⟨entry, hentry, heq⟩
    apply hfresh
    refine ⟨entry, ?_, heq⟩
    rw [Generic.CappedChain.AttackerActionTrace.toSigningLog_append]
    exact List.mem_append_left _ hentry
  rw [signing_preserves_fresh_encoding secretKey request forgery hne cache finalCache answer hsign] at hcache
  exact ⟨forgery, output, holdFresh, hcache, hvalid⟩

theorem hasFreshAcceptedEncoding_query_le (publicKey : PublicKey) (secretKey : Generic.SecretKey)
    (input : (OracleWorld + Generic.SigningSpec).Domain) (state : Generic.CappedChain.SourceTracedState)
    (hstate : ¬ HasFreshAcceptedEncoding secretKey.parameter state) :
    Pr[fun result => HasFreshAcceptedEncoding secretKey.parameter result.2 |
      (Generic.CappedChain.sourceDirectTracedMappedAdversaryImpl publicKey secretKey input).run state] ≤
      if IsDirectEncodingQuery secretKey.parameter input then TargetSum.acceptanceProbability else 0 := by
  classical
  rcases state with ⟨cache, trace⟩
  rcases input with (uniformInput | hashInput) | request
  · rw [if_neg (by simp [IsDirectEncodingQuery, Generic.CappedEncodingMonitor.IsEncodingHashQuery])]
    apply le_of_eq
    apply probEvent_eq_zero
    intro result hresult hevent
    rw [Generic.CappedChain.sourceDirectTracedMappedAdversaryImpl, Generic.CappedChain.actionTracedStateImpl, StateT.run_mk,
      mem_support_bind_iff] at hresult
    obtain ⟨⟨answer, finalCache⟩, hquery, hpure⟩ := hresult
    simp only [support_pure, Set.mem_singleton_iff] at hpure
    subst result
    have hcache := Generic.cappedUnloggedMappedAdversaryImpl_uniform_cache_eq publicKey secretKey uniformInput
      cache (answer, finalCache) hquery
    change finalCache = cache at hcache
    exact hstate (by simpa only [Generic.CappedChain.attackerActionFragment_uniform, List.append_nil, hcache] using hevent)
  · have hrun : (Generic.CappedChain.sourceDirectTracedMappedAdversaryImpl publicKey secretKey (.inl (.inr hashInput))).run
        (cache, trace) = (fun result : Digest × QueryCache HashSpec =>
          (result.1, (result.2, trace ++ [.hash hashInput]))) <$>
            (randomOracle (spec := HashSpec) hashInput).run cache := by
      simp only [Generic.CappedChain.sourceDirectTracedMappedAdversaryImpl, Generic.CappedChain.actionTracedStateImpl, StateT.run_mk,
        bind_pure_comp]
      rfl
    rw [hrun, probEvent_map]
    simp only [Function.comp_def, hasFreshAcceptedEncoding_append_hash]
    cases hcached : cache hashInput with
    | some output =>
        rw [QueryImpl.withCaching_run_some _ hcached]
        simp only [probEvent_pure, if_neg hstate]
        exact zero_le
    | none =>
        rw [Generic.randomOracle_run_none_eq_uniformHashOutput _ _ hcached, probEvent_map]
        by_cases hencoding : (Generic.encodingInputLeafIndex? secretKey.parameter hashInput).isSome
        · rw [if_pos (by exact hencoding)]
          apply le_trans _ TargetSum.probEvent_validDigest_uniform.le
          apply probEvent_mono''
          intro output hnew
          exact (hasFreshAcceptedEncoding_cacheQuery _ _ _ _ _ hstate hnew).2
        · rw [if_neg (by exact hencoding)]
          apply le_of_eq
          apply probEvent_eq_zero
          intro output _ hnew
          exact hencoding (hasFreshAcceptedEncoding_cacheQuery _ _ _ _ _ hstate hnew).1
  · rw [if_neg (by simp [IsDirectEncodingQuery])]
    apply le_of_eq
    apply probEvent_eq_zero
    intro result hresult hevent
    rw [Generic.CappedChain.sourceDirectTracedMappedAdversaryImpl, Generic.CappedChain.actionTracedStateImpl, StateT.run_mk,
      mem_support_bind_iff] at hresult
    obtain ⟨⟨answer, finalCache⟩, hquery, hpure⟩ := hresult
    simp only [support_pure, Set.mem_singleton_iff] at hpure
    subst result
    exact hstate (hasFreshAcceptedEncoding_signing secretKey request cache finalCache trace answer hquery hevent)

theorem probEvent_freshAccepted_le_expected_directEncoding (publicKey : PublicKey) (secretKey : Generic.SecretKey)
    {α : Type} (computation : OracleComp (OracleWorld + Generic.SigningSpec) α) (state : Generic.CappedChain.SourceTracedState)
    (hstate : ¬ HasFreshAcceptedEncoding secretKey.parameter state) :
    Pr[fun result => HasFreshAcceptedEncoding secretKey.parameter result.2 |
      (simulateQ (Generic.CappedChain.sourceDirectTracedMappedAdversaryImpl publicKey secretKey) computation).run state] ≤
      TargetSum.acceptanceProbability * expectedSimulatedQueryCount
        (Generic.CappedChain.sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
        (IsDirectEncodingQuery secretKey.parameter) computation state := by
  simpa only [if_neg hstate, zero_add] using
    probEvent_state_le_initial_add_expectedQueryCount (Generic.CappedChain.sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
      (IsDirectEncodingQuery secretKey.parameter) (HasFreshAcceptedEncoding secretKey.parameter)
      TargetSum.acceptanceProbability (hasFreshAcceptedEncoding_query_le publicKey secretKey)
      computation state

theorem hasFreshAcceptedEncoding_of_decode (parameter : PublicParameter)
    (state : Generic.CappedChain.SourceTracedState) (forgery : Generic.Forgery) (encoding : Encoding)
    (hfresh : ¬ SigningTranscript.ContainsRequest state.2.toSigningLog forgery)
    (hdecode : Generic.Code.decodeDigest (Generic.Concrete.CacheView.encodingHash state.1 parameter forgery.epoch
      (forgery.message, forgery.signature.randomness)) = some encoding) :
    HasFreshAcceptedEncoding parameter state := by
  obtain ⟨output, hcached⟩ := TargetSum.encodingInput_cached_of_decode_some state.1 parameter
    forgery.epoch forgery.message forgery.signature.randomness encoding hdecode
  refine ⟨forgery, output, hfresh, hcached, encoding, ?_⟩
  simpa [Generic.Concrete.CacheView.encodingHash, Generic.Concrete.CacheView.digestAt, hcached] using hdecode

theorem no_freshAcceptedEncoding_of_no_encodingInputs (parameter : PublicParameter)
    (cache : QueryCache HashSpec) (trace : Generic.AttackerActionTrace)
    (hempty : ∀ leaf payload, cache (Generic.Concrete.CacheView.encodingInput parameter leaf payload) = none) :
    ¬ HasFreshAcceptedEncoding parameter (cache, trace) := by
  rintro ⟨forgery, output, _, hcache, _⟩
  dsimp only at hcache
  rw [hempty] at hcache
  contradiction

theorem isDirectEncodingQuery_implies_directHash (parameter : PublicParameter)
    (input : (OracleWorld + Generic.SigningSpec).Domain) (h : IsDirectEncodingQuery parameter input) :
    Generic.Direct.IsDirectHashQuery input := by
  rcases input with (uniformInput | hashInput) | request
  · simp [IsDirectEncodingQuery, Generic.CappedEncodingMonitor.IsEncodingHashQuery] at h
  · rfl
  · exact h.elim

/-- A direct-query budget bounds fresh accepted encodings independently of signing cost. -/
theorem probEvent_freshAccepted_le_direct_budget (publicKey : PublicKey) (secretKey : Generic.SecretKey)
    {α : Type} (computation : OracleComp (OracleWorld + Generic.SigningSpec) α) (cache : QueryCache HashSpec)
    (hempty : ∀ leaf payload, cache (Generic.Concrete.CacheView.encodingInput secretKey.parameter leaf payload) = none)
    (D : ℕ) (hD : computation.IsQueryBoundP Generic.Direct.IsDirectHashQuery D) :
    Pr[fun result => HasFreshAcceptedEncoding secretKey.parameter result.2 |
      (simulateQ (Generic.CappedChain.sourceDirectTracedMappedAdversaryImpl publicKey secretKey) computation).run (cache, [])] ≤
      TargetSum.acceptanceProbability * (D : ℝ≥0∞) := by
  apply (probEvent_freshAccepted_le_expected_directEncoding publicKey secretKey computation (cache, [])
    (no_freshAcceptedEncoding_of_no_encodingInputs _ _ _ hempty)).trans
  apply mul_le_mul' le_rfl
  exact expectedSimulatedQueryCount_le_of_isQueryBoundP _ _ computation (cache, []) D
    (hD.of_imp (isDirectEncodingQuery_implies_directHash secretKey.parameter))

/-- info: 'XmssSecurity.TargetSum.EUFCMA.probEvent_freshAccepted_le_expected_directEncoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms probEvent_freshAccepted_le_expected_directEncoding

/-- info: 'XmssSecurity.TargetSum.EUFCMA.probEvent_freshAccepted_le_direct_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms probEvent_freshAccepted_le_direct_budget

end XmssSecurity.TargetSum.EUFCMA
