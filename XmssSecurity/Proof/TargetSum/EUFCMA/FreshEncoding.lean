import XmssSecurity.Proof.TargetSum.EUFCMA.Execution
import XmssSecurity.Proof.TargetSum.Attack.MutationSigningCache
import XmssSecurity.Proof.TargetSum.CappedChain.SourceDirectTrace
import XmssSecurity.Proof.TargetSum.CappedEncodingActionTrace

/-! A standard-fresh encoding input cannot be supplied by free signing requests.
The reference signer changes encoding entries only for the requested input. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.EUFCMA
open XmssSecurity.EUFCMA

open Concrete CappedChain

theorem encodingInput_ne_of_request_ne (parameter : PublicParameter)
    (request : SignRequest) (forgery : Forgery) (hne : request ≠ forgery.request)
    (randomness : Randomness) :
    CacheView.encodingInput parameter request.epoch (request.message, randomness) ≠
      CacheView.encodingInput parameter forgery.epoch (forgery.message, forgery.signature.randomness) := by
  intro heq
  obtain ⟨hepoch, hpayload⟩ := (CacheView.encodingInput_eq_iff _ _ _ _ _).1 heq
  exact hne (congrArg₂ SUFCMA.SignRequest.mk hepoch (congrArg Prod.fst hpayload))

theorem signing_preserves_fresh_encoding (secretKey : SecretKey)
    (request : SignRequest) (forgery : Forgery) (hne : request ≠ forgery.request)
    (initialCache finalCache : QueryCache HashSpec) (answer : Option Signature)
    (hsign : (answer, finalCache) ∈ support ((simulateQ romImpl
      (precomputedCappedSign secretKey request.epoch request.message)).run initialCache)) :
    finalCache (CacheView.encodingInput secretKey.parameter forgery.epoch
        (forgery.message, forgery.signature.randomness)) =
      initialCache (CacheView.encodingInput secretKey.parameter forgery.epoch
        (forgery.message, forgery.signature.randomness)) := by
  rw [precomputedCappedSign] at hsign
  exact precomputedSignBoundedAttempts_preserves_unqueriedInput signingAttemptLimit secretKey
    request.epoch request.message _
    (encodingInput_ne_of_request_ne secretKey.parameter request forgery hne)
    initialCache finalCache answer hsign

/-- Unrequested and directly unqueried encoding entries retain their initial value. -/
def FreshEncodingCache (secretKey : SecretKey) (initialCache : QueryCache HashSpec)
    (state : SourceTracedState) : Prop :=
  ∀ forgery : Forgery,
    ¬ SigningTranscript.ContainsRequest state.2.toSigningLog forgery →
    CacheView.encodingInput secretKey.parameter forgery.epoch
      (forgery.message, forgery.signature.randomness) ∉ state.2.hashInputs →
    state.1 (CacheView.encodingInput secretKey.parameter forgery.epoch
      (forgery.message, forgery.signature.randomness)) =
      initialCache (CacheView.encodingInput secretKey.parameter forgery.epoch
        (forgery.message, forgery.signature.randomness))

theorem freshEncodingCache_initial (secretKey : SecretKey) (cache : QueryCache HashSpec) :
    FreshEncodingCache secretKey cache (cache, []) := by
  intro forgery _ _
  rfl

theorem freshEncodingCache_query (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) (input : (OracleWorld + SigningSpec).Domain)
    (state : SourceTracedState) (hstate : FreshEncodingCache secretKey initialCache state)
    (result : (OracleWorld + SigningSpec).Range input × SourceTracedState)
    (hresult : result ∈ support ((sourceDirectTracedMappedAdversaryImpl publicKey secretKey input).run state)) :
    FreshEncodingCache secretKey initialCache result.2 := by
  rw [sourceDirectTracedMappedAdversaryImpl, actionTracedStateImpl, StateT.run_mk,
    mem_support_bind_iff] at hresult
  obtain ⟨⟨answer, cache⟩, hquery, hpure⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  intro forgery hfresh hunqueried
  have hfreshOld : ¬ SigningTranscript.ContainsRequest state.2.toSigningLog forgery := by
    intro h
    apply hfresh
    obtain ⟨entry, hentry, heq⟩ := h
    exact ⟨entry, by rw [AttackerActionTrace.toSigningLog_append]; exact List.mem_append_left _ hentry, heq⟩
  have hunqueriedOld : CacheView.encodingInput secretKey.parameter forgery.epoch
      (forgery.message, forgery.signature.randomness) ∉ state.2.hashInputs := by
    intro h
    apply hunqueried
    rw [AttackerActionTrace.hashInputs_append]
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
      simp [heq, AttackerActionTrace.hashInputs, AttackerAction.hashInput?]
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
    simp [AttackerActionTrace.toSigningLog, AttackerAction.signingEntry?]

theorem freshEncodingCache_execution (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) {α : Type}
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (result : α × SourceTracedState)
    (hresult : result ∈ support ((simulateQ (sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
      computation).run (initialCache, []))) :
    FreshEncodingCache secretKey initialCache result.2 :=
  OracleComp.simulateQ_run_preservesInv (sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
    (FreshEncodingCache secretKey initialCache)
    (freshEncodingCache_query publicKey secretKey initialCache)
    computation (initialCache, []) (freshEncodingCache_initial secretKey initialCache) result hresult

/-- info: 'XmssSecurity.TargetSum.EUFCMA.freshEncodingCache_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms freshEncodingCache_execution

end XmssSecurity.TargetSum.EUFCMA
