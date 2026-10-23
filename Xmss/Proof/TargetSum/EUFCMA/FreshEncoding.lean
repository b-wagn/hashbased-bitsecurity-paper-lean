import Xmss.Proof.TargetSum.EUFCMA.Execution
import Xmss.Proof.Generic.Attack.MutationSigningCache
import Xmss.Proof.Generic.CappedExecution.SourceDirectTrace
import Xmss.Proof.Generic.CappedEncodingActionTrace
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability
/-! A standard-fresh encoding input cannot be supplied by free signing requests.
The reference signer changes encoding entries only for the requested input. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum.EUFCMA
open Xmss.EUFCMA

open Hashing Wots Merkle Verify Keygen Signing CappedExecution

theorem encodingInput_ne_of_request_ne (parameter : PublicParameter)
    (request : SignRequest) (forgery : Forgery) (hne : request ≠ forgery.request)
    (randomness : Randomness) :
    CacheView.encodingInput parameter request.epoch (request.message, randomness) ≠
      CacheView.encodingInput parameter forgery.epoch (forgery.message, forgery.signature.randomness) := by
  intro heq
  obtain ⟨hepoch, hpayload⟩ := (CacheView.encodingInput_eq_iff _ _ _ _ _).1 heq
  exact hne (congrArg₂ Unforgeability.SignRequest.mk hepoch (congrArg Prod.fst hpayload))

theorem signing_preserves_fresh_encoding (secretKey : Generic.SecretKey)
    (request : SignRequest) (forgery : Forgery) (hne : request ≠ forgery.request)
    (initialCache finalCache : QueryCache HashSpec) (answer : Option Generic.Signature)
    (hsign : (answer, finalCache) ∈ support ((simulateQ romImpl
      (Signing.precomputedCappedSign secretKey request.epoch request.message)).run initialCache)) :
    finalCache (CacheView.encodingInput secretKey.parameter forgery.epoch
        (forgery.message, forgery.signature.randomness)) =
      initialCache (CacheView.encodingInput secretKey.parameter forgery.epoch
        (forgery.message, forgery.signature.randomness)) := by
  rw [Signing.precomputedCappedSign] at hsign
  exact Signing.precomputedSignBoundedAttempts_preserves_unqueriedInput signingAttemptLimit secretKey
    request.epoch request.message _
    (encodingInput_ne_of_request_ne secretKey.parameter request forgery hne)
    initialCache finalCache answer hsign

/-- Unrequested and directly unqueried encoding entries retain their initial value. -/
def FreshEncodingCache (secretKey : Generic.SecretKey) (initialCache : QueryCache HashSpec)
    (state : CappedExecution.SourceTracedState) : Prop :=
  ∀ forgery : Forgery,
    ¬ Unforgeability.SigningTranscript.ContainsRequest state.2.toSigningLog forgery →
    CacheView.encodingInput secretKey.parameter forgery.epoch
      (forgery.message, forgery.signature.randomness) ∉ state.2.hashInputs →
    state.1 (CacheView.encodingInput secretKey.parameter forgery.epoch
      (forgery.message, forgery.signature.randomness)) =
      initialCache (CacheView.encodingInput secretKey.parameter forgery.epoch
        (forgery.message, forgery.signature.randomness))

theorem freshEncodingCache_initial (secretKey : Generic.SecretKey) (cache : QueryCache HashSpec) :
    FreshEncodingCache secretKey cache (cache, []) := by
  intro forgery _ _
  rfl

theorem freshEncodingCache_query (publicKey : PublicKey) (secretKey : Generic.SecretKey)
    (initialCache : QueryCache HashSpec) (input : (OracleWorld + SigningSpec).Domain)
    (state : CappedExecution.SourceTracedState) (hstate : FreshEncodingCache secretKey initialCache state)
    (result : (OracleWorld + SigningSpec).Range input × CappedExecution.SourceTracedState)
    (hresult : result ∈ support ((CappedExecution.sourceDirectTracedMappedAdversaryImpl publicKey secretKey input).run state)) :
    FreshEncodingCache secretKey initialCache result.2 := by
  rw [CappedExecution.sourceDirectTracedMappedAdversaryImpl, CappedExecution.actionTracedStateImpl, StateT.run_mk,
    mem_support_bind_iff] at hresult
  obtain ⟨⟨answer, cache⟩, hquery, hpure⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  intro forgery hfresh hunqueried
  have hfreshOld : ¬ Unforgeability.SigningTranscript.ContainsRequest state.2.toSigningLog forgery := by
    intro h
    apply hfresh
    obtain ⟨entry, hentry, heq⟩ := h
    exact ⟨entry, by rw [CappedExecution.AttackerActionTrace.toSigningLog_append]; exact List.mem_append_left _ hentry, heq⟩
  have hunqueriedOld : CacheView.encodingInput secretKey.parameter forgery.epoch
      (forgery.message, forgery.signature.randomness) ∉ state.2.hashInputs := by
    intro h
    apply hunqueried
    rw [CappedExecution.AttackerActionTrace.hashInputs_append]
    exact List.mem_append_left _ h
  apply Eq.trans _ (hstate forgery hfreshOld hunqueriedOld)
  rcases input with (uniformInput | hashInput) | request
  · exact congrArg (fun c : QueryCache HashSpec => c _)
      (cappedUnloggedMappedAdversaryImpl_uniform_cache_eq publicKey secretKey uniformInput
        state.1 (answer, cache) hquery)
  · have hne : hashInput ≠ CacheView.encodingInput secretKey.parameter forgery.epoch
        (forgery.message, forgery.signature.randomness) := by
      intro heq
      apply hunqueried
      simp [heq, CappedExecution.AttackerActionTrace.hashInputs, CappedExecution.AttackerAction.hashInput?]
    change (answer, cache) ∈ support ((randomOracle (spec := HashSpec) hashInput).run state.1) at hquery
    cases hcached : state.1 hashInput with
    | none =>
        rw [QueryImpl.withCaching_run_none _ hcached, support_map] at hquery
        obtain ⟨sampled, _, heq⟩ := hquery
        cases heq
        exact QueryCache.cacheQuery_of_ne _ _ (Ne.symm hne)
    | some output =>
        rw [QueryImpl.withCaching_run_some _ hcached, support_pure, Set.mem_singleton_iff] at hquery
        cases hquery
        rfl
  · apply signing_preserves_fresh_encoding secretKey request forgery _ state.1 cache answer hquery
    intro heq
    apply hfresh
    refine ⟨⟨request, answer⟩, ?_, heq⟩
    simp [CappedExecution.AttackerActionTrace.toSigningLog, CappedExecution.AttackerAction.signingEntry?]

theorem freshEncodingCache_execution (publicKey : PublicKey) (secretKey : Generic.SecretKey)
    (initialCache : QueryCache HashSpec) {α : Type}
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (result : α × CappedExecution.SourceTracedState)
    (hresult : result ∈ support ((simulateQ (CappedExecution.sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
      computation).run (initialCache, []))) :
    FreshEncodingCache secretKey initialCache result.2 :=
  OracleComp.simulateQ_run_preservesInv (CappedExecution.sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
    (FreshEncodingCache secretKey initialCache)
    (freshEncodingCache_query publicKey secretKey initialCache)
    computation (initialCache, []) (freshEncodingCache_initial secretKey initialCache) result hresult

/-- info: 'Xmss.TargetSum.EUFCMA.freshEncodingCache_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms freshEncodingCache_execution

end Xmss.TargetSum.EUFCMA
