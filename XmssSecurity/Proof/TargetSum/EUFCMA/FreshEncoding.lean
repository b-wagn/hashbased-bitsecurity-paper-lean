import XmssSecurity.Proof.TargetSum.EUFCMA.Execution
import XmssSecurity.Proof.Generic.Attack.MutationSigningCache
import XmssSecurity.Proof.Generic.CappedChain.SourceDirectTrace
import XmssSecurity.Proof.Generic.CappedEncodingActionTrace
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability
/-! A standard-fresh encoding input cannot be supplied by free signing requests.
The reference signer changes encoding entries only for the requested input. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.EUFCMA
open XmssSecurity.EUFCMA

open Concrete CappedChain

theorem encodingInput_ne_of_request_ne (parameter : PublicParameter)
    (request : SignRequest) (forgery : Forgery) (hne : request ≠ forgery.request)
    (randomness : Randomness) :
    Concrete.CacheView.encodingInput parameter request.epoch (request.message, randomness) ≠
      Concrete.CacheView.encodingInput parameter forgery.epoch (forgery.message, forgery.signature.randomness) := by
  intro heq
  obtain ⟨hepoch, hpayload⟩ := (Concrete.CacheView.encodingInput_eq_iff _ _ _ _ _).1 heq
  exact hne (congrArg₂ SUFCMA.SignRequest.mk hepoch (congrArg Prod.fst hpayload))

theorem signing_preserves_fresh_encoding (secretKey : Generic.SecretKey)
    (request : SignRequest) (forgery : Forgery) (hne : request ≠ forgery.request)
    (initialCache finalCache : QueryCache HashSpec) (answer : Option Generic.Signature)
    (hsign : (answer, finalCache) ∈ support ((simulateQ romImpl
      (Concrete.precomputedCappedSign secretKey request.epoch request.message)).run initialCache)) :
    finalCache (Concrete.CacheView.encodingInput secretKey.parameter forgery.epoch
        (forgery.message, forgery.signature.randomness)) =
      initialCache (Concrete.CacheView.encodingInput secretKey.parameter forgery.epoch
        (forgery.message, forgery.signature.randomness)) := by
  rw [Concrete.precomputedCappedSign] at hsign
  exact Concrete.precomputedSignBoundedAttempts_preserves_unqueriedInput signingAttemptLimit secretKey
    request.epoch request.message _
    (encodingInput_ne_of_request_ne secretKey.parameter request forgery hne)
    initialCache finalCache answer hsign

/-- Unrequested and directly unqueried encoding entries retain their initial value. -/
def FreshEncodingCache (secretKey : Generic.SecretKey) (initialCache : QueryCache HashSpec)
    (state : CappedChain.SourceTracedState) : Prop :=
  ∀ forgery : Forgery,
    ¬ SigningTranscript.ContainsRequest state.2.toSigningLog forgery →
    Concrete.CacheView.encodingInput secretKey.parameter forgery.epoch
      (forgery.message, forgery.signature.randomness) ∉ state.2.hashInputs →
    state.1 (Concrete.CacheView.encodingInput secretKey.parameter forgery.epoch
      (forgery.message, forgery.signature.randomness)) =
      initialCache (Concrete.CacheView.encodingInput secretKey.parameter forgery.epoch
        (forgery.message, forgery.signature.randomness))

theorem freshEncodingCache_initial (secretKey : Generic.SecretKey) (cache : QueryCache HashSpec) :
    FreshEncodingCache secretKey cache (cache, []) := by
  intro forgery _ _
  rfl

theorem freshEncodingCache_query (publicKey : PublicKey) (secretKey : Generic.SecretKey)
    (initialCache : QueryCache HashSpec) (input : (OracleWorld + SigningSpec).Domain)
    (state : CappedChain.SourceTracedState) (hstate : FreshEncodingCache secretKey initialCache state)
    (result : (OracleWorld + SigningSpec).Range input × CappedChain.SourceTracedState)
    (hresult : result ∈ support ((CappedChain.sourceDirectTracedMappedAdversaryImpl publicKey secretKey input).run state)) :
    FreshEncodingCache secretKey initialCache result.2 := by
  rw [CappedChain.sourceDirectTracedMappedAdversaryImpl, CappedChain.actionTracedStateImpl, StateT.run_mk,
    mem_support_bind_iff] at hresult
  obtain ⟨⟨answer, cache⟩, hquery, hpure⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  intro forgery hfresh hunqueried
  have hfreshOld : ¬ SigningTranscript.ContainsRequest state.2.toSigningLog forgery := by
    intro h
    apply hfresh
    obtain ⟨entry, hentry, heq⟩ := h
    exact ⟨entry, by rw [CappedChain.AttackerActionTrace.toSigningLog_append]; exact List.mem_append_left _ hentry, heq⟩
  have hunqueriedOld : Concrete.CacheView.encodingInput secretKey.parameter forgery.epoch
      (forgery.message, forgery.signature.randomness) ∉ state.2.hashInputs := by
    intro h
    apply hunqueried
    rw [CappedChain.AttackerActionTrace.hashInputs_append]
    exact List.mem_append_left _ h
  apply Eq.trans _ (hstate forgery hfreshOld hunqueriedOld)
  rcases input with (uniformInput | hashInput) | request
  · exact congrArg (fun c : QueryCache HashSpec => c _)
      (cappedUnloggedMappedAdversaryImpl_uniform_cache_eq publicKey secretKey uniformInput
        state.1 (answer, cache) hquery)
  · have hne : hashInput ≠ Concrete.CacheView.encodingInput secretKey.parameter forgery.epoch
        (forgery.message, forgery.signature.randomness) := by
      intro heq
      apply hunqueried
      simp [heq, CappedChain.AttackerActionTrace.hashInputs, CappedChain.AttackerAction.hashInput?]
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
    simp [CappedChain.AttackerActionTrace.toSigningLog, CappedChain.AttackerAction.signingEntry?]

theorem freshEncodingCache_execution (publicKey : PublicKey) (secretKey : Generic.SecretKey)
    (initialCache : QueryCache HashSpec) {α : Type}
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (result : α × CappedChain.SourceTracedState)
    (hresult : result ∈ support ((simulateQ (CappedChain.sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
      computation).run (initialCache, []))) :
    FreshEncodingCache secretKey initialCache result.2 :=
  OracleComp.simulateQ_run_preservesInv (CappedChain.sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
    (FreshEncodingCache secretKey initialCache)
    (freshEncodingCache_query publicKey secretKey initialCache)
    computation (initialCache, []) (freshEncodingCache_initial secretKey initialCache) result hresult

/-- info: 'XmssSecurity.TargetSum.EUFCMA.freshEncodingCache_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms freshEncodingCache_execution

end XmssSecurity.TargetSum.EUFCMA
