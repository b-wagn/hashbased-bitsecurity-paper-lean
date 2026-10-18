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

namespace XmssSecurity.TargetSum.EUFCMA
open XmssSecurity.EUFCMA

open Concrete Generic.CappedChain

theorem encodingInput_ne_of_request_ne (parameter : PublicParameter)
    (request : Generic.SignRequest) (forgery : Generic.Forgery) (hne : request ≠ forgery.request)
    (randomness : Randomness) :
    Generic.Concrete.CacheView.encodingInput parameter request.epoch (request.message, randomness) ≠
      Generic.Concrete.CacheView.encodingInput parameter forgery.epoch (forgery.message, forgery.signature.randomness) := by
  intro heq
  obtain ⟨hepoch, hpayload⟩ := (Generic.Concrete.CacheView.encodingInput_eq_iff _ _ _ _ _).1 heq
  exact hne (congrArg₂ SUFCMA.SignRequest.mk hepoch (congrArg Prod.fst hpayload))

theorem signing_preserves_fresh_encoding (secretKey : Generic.SecretKey)
    (request : Generic.SignRequest) (forgery : Generic.Forgery) (hne : request ≠ forgery.request)
    (initialCache finalCache : QueryCache HashSpec) (answer : Option Generic.Signature)
    (hsign : (answer, finalCache) ∈ support ((simulateQ Generic.romImpl
      (Generic.Concrete.precomputedCappedSign secretKey request.epoch request.message)).run initialCache)) :
    finalCache (Generic.Concrete.CacheView.encodingInput secretKey.parameter forgery.epoch
        (forgery.message, forgery.signature.randomness)) =
      initialCache (Generic.Concrete.CacheView.encodingInput secretKey.parameter forgery.epoch
        (forgery.message, forgery.signature.randomness)) := by
  rw [Generic.Concrete.precomputedCappedSign] at hsign
  exact Generic.Concrete.precomputedSignBoundedAttempts_preserves_unqueriedInput signingAttemptLimit secretKey
    request.epoch request.message _
    (encodingInput_ne_of_request_ne secretKey.parameter request forgery hne)
    initialCache finalCache answer hsign

/-- Unrequested and directly unqueried encoding entries retain their initial value. -/
def FreshEncodingCache (secretKey : Generic.SecretKey) (initialCache : QueryCache HashSpec)
    (state : Generic.CappedChain.SourceTracedState) : Prop :=
  ∀ forgery : Generic.Forgery,
    ¬ SigningTranscript.ContainsRequest state.2.toSigningLog forgery →
    Generic.Concrete.CacheView.encodingInput secretKey.parameter forgery.epoch
      (forgery.message, forgery.signature.randomness) ∉ state.2.hashInputs →
    state.1 (Generic.Concrete.CacheView.encodingInput secretKey.parameter forgery.epoch
      (forgery.message, forgery.signature.randomness)) =
      initialCache (Generic.Concrete.CacheView.encodingInput secretKey.parameter forgery.epoch
        (forgery.message, forgery.signature.randomness))

theorem freshEncodingCache_initial (secretKey : Generic.SecretKey) (cache : QueryCache HashSpec) :
    FreshEncodingCache secretKey cache (cache, []) := by
  intro forgery _ _
  rfl

theorem freshEncodingCache_query (publicKey : PublicKey) (secretKey : Generic.SecretKey)
    (initialCache : QueryCache HashSpec) (input : (OracleWorld + Generic.SigningSpec).Domain)
    (state : Generic.CappedChain.SourceTracedState) (hstate : FreshEncodingCache secretKey initialCache state)
    (result : (OracleWorld + Generic.SigningSpec).Range input × Generic.CappedChain.SourceTracedState)
    (hresult : result ∈ support ((Generic.CappedChain.sourceDirectTracedMappedAdversaryImpl publicKey secretKey input).run state)) :
    FreshEncodingCache secretKey initialCache result.2 := by
  rw [Generic.CappedChain.sourceDirectTracedMappedAdversaryImpl, Generic.CappedChain.actionTracedStateImpl, StateT.run_mk,
    mem_support_bind_iff] at hresult
  obtain ⟨⟨answer, cache⟩, hquery, hpure⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  intro forgery hfresh hunqueried
  have hfreshOld : ¬ SigningTranscript.ContainsRequest state.2.toSigningLog forgery := by
    intro h
    apply hfresh
    obtain ⟨entry, hentry, heq⟩ := h
    exact ⟨entry, by rw [Generic.CappedChain.AttackerActionTrace.toSigningLog_append]; exact List.mem_append_left _ hentry, heq⟩
  have hunqueriedOld : Generic.Concrete.CacheView.encodingInput secretKey.parameter forgery.epoch
      (forgery.message, forgery.signature.randomness) ∉ state.2.hashInputs := by
    intro h
    apply hunqueried
    rw [Generic.CappedChain.AttackerActionTrace.hashInputs_append]
    exact List.mem_append_left _ h
  apply Eq.trans _ (hstate forgery hfreshOld hunqueriedOld)
  rcases input with (uniformInput | hashInput) | request
  · exact congrArg (fun c : QueryCache HashSpec => c _)
      (Generic.cappedUnloggedMappedAdversaryImpl_uniform_cache_eq publicKey secretKey uniformInput
        state.1 (answer, cache) hquery)
  · have hne : hashInput ≠ Generic.Concrete.CacheView.encodingInput secretKey.parameter forgery.epoch
        (forgery.message, forgery.signature.randomness) := by
      intro heq
      apply hunqueried
      simp [heq, Generic.CappedChain.AttackerActionTrace.hashInputs, Generic.CappedChain.AttackerAction.hashInput?]
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
    simp [Generic.CappedChain.AttackerActionTrace.toSigningLog, Generic.CappedChain.AttackerAction.signingEntry?]

theorem freshEncodingCache_execution (publicKey : PublicKey) (secretKey : Generic.SecretKey)
    (initialCache : QueryCache HashSpec) {α : Type}
    (computation : OracleComp (OracleWorld + Generic.SigningSpec) α)
    (result : α × Generic.CappedChain.SourceTracedState)
    (hresult : result ∈ support ((simulateQ (Generic.CappedChain.sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
      computation).run (initialCache, []))) :
    FreshEncodingCache secretKey initialCache result.2 :=
  OracleComp.simulateQ_run_preservesInv (Generic.CappedChain.sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
    (FreshEncodingCache secretKey initialCache)
    (freshEncodingCache_query publicKey secretKey initialCache)
    computation (initialCache, []) (freshEncodingCache_initial secretKey initialCache) result hresult

/-- info: 'XmssSecurity.TargetSum.EUFCMA.freshEncodingCache_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms freshEncodingCache_execution

end XmssSecurity.TargetSum.EUFCMA
