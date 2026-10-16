import XmssSecurity.Proof.Direct.SourceBudgetExhaustion
import XmssSecurity.Proof.Direct.MixedFirstLane

/-! At an exhausted budget, a cache without an accepted encoding cannot produce
a cached first-lane witness. Actual verification retains its fresh acceptance factor. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.Deciding

open Concrete CappedChain Direct

theorem exhaustedSource_acceptedPrefix_probability_eq_zero
    (key : ProgrammedGlobalChainKeygenView) (limit : Nat)
    (computation : OracleComp (OracleWorld + SigningSpec) Forgery) (state : CountedSourceState)
    (hbudget : CountedSourceBudget (materializePrecomputation key.cache key.secretKey)
      limit computation state) (hexhausted : limit ≤ state.charge)
    (hcache : ¬HasAcceptedEncoding key.secretKey.parameter state.counts.cache) :
    Pr[fun result => AcceptedPrefixFirstLaneEvent key (result.1, result.2.toSource) |
      (simulateQ (countedSourceImpl (materializePrecomputation key.cache key.secretKey)) computation).run state] = 0 := by
  apply probEvent_eq_zero
  intro result hresult hevent
  exact (hbudget.noAcceptedEncoding_of_exhausted hexhausted hcache result hresult)
    (acceptedPrefixFirstLane_implies_accepted key result hevent)

theorem lastNonencodingSource_acceptedPrefix_probability_eq_zero
    (key : ProgrammedGlobalChainKeygenView) (limit : Nat) (input : HashInput)
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) Forgery) (state : CountedSourceState)
    (hbudget : CountedSourceBudget (materializePrecomputation key.cache key.secretKey) limit
      (liftM ((OracleWorld + SigningSpec).query (.inl (.inr input))) >>= next) state)
    (hlast : limit ≤ state.charge + 1)
    (hcache : ¬HasAcceptedEncoding key.secretKey.parameter state.counts.cache)
    (hinput : ¬CappedEncodingMonitor.IsEncodingHashQuery key.secretKey.parameter (.inr input)) :
    Pr[fun result => AcceptedPrefixFirstLaneEvent key (result.1, result.2.toSource) |
      (simulateQ (countedSourceImpl (materializePrecomputation key.cache key.secretKey))
        (liftM ((OracleWorld + SigningSpec).query (.inl (.inr input))) >>= next)).run state] = 0 := by
  apply probEvent_eq_zero
  intro result hresult hevent
  exact (hbudget.noAcceptedEncoding_after_last_nonencoding hlast hcache hinput result hresult)
    (acceptedPrefixFirstLane_implies_accepted key result hevent)

theorem exhaustedSource_firstLane_probability_le_acceptance
    (key : ProgrammedGlobalChainKeygenView) (limit : Nat)
    (hparameter : key.publicKey.parameter = key.secretKey.parameter)
    (computation : OracleComp (OracleWorld + SigningSpec) Forgery) (state : CountedSourceState)
    (hbudget : CountedSourceBudget (materializePrecomputation key.cache key.secretKey)
      limit computation state) (hexhausted : limit ≤ state.charge)
    (hcache : ¬HasAcceptedEncoding key.secretKey.parameter state.counts.cache) :
    Pr[SourceWinningDecidingFirstLaneEvent | do
      let result ← (simulateQ (countedSourceImpl (materializePrecomputation key.cache key.secretKey))
        computation).run state
      let finished ← sourcePrefixFinish key (result.1, result.2.toSource)
      pure (key, finished)] ≤ Checksum.acceptanceProbability := by
  apply probEvent_bind_le_of_forall_le
  intro result hresult
  simp only [bind_pure_comp, probEvent_map, Function.comp_def]
  apply sourcePrefixFinish_firstLane_probability_le_acceptance_of_noAcceptedEncoding
  change ¬HasAcceptedEncoding key.publicKey.parameter result.2.counts.cache
  rw [hparameter]
  exact hbudget.noAcceptedEncoding_of_exhausted hexhausted hcache result hresult

theorem lastNonencodingSource_firstLane_probability_le_acceptance
    (key : ProgrammedGlobalChainKeygenView) (limit : Nat) (input : HashInput)
    (hparameter : key.publicKey.parameter = key.secretKey.parameter)
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) Forgery) (state : CountedSourceState)
    (hbudget : CountedSourceBudget (materializePrecomputation key.cache key.secretKey) limit
      (liftM ((OracleWorld + SigningSpec).query (.inl (.inr input))) >>= next) state)
    (hlast : limit ≤ state.charge + 1)
    (hcache : ¬HasAcceptedEncoding key.secretKey.parameter state.counts.cache)
    (hinput : ¬CappedEncodingMonitor.IsEncodingHashQuery key.secretKey.parameter (.inr input)) :
    Pr[SourceWinningDecidingFirstLaneEvent | do
      let result ← (simulateQ (countedSourceImpl (materializePrecomputation key.cache key.secretKey))
        (liftM ((OracleWorld + SigningSpec).query (.inl (.inr input))) >>= next)).run state
      let finished ← sourcePrefixFinish key (result.1, result.2.toSource)
      pure (key, finished)] ≤ Checksum.acceptanceProbability := by
  apply probEvent_bind_le_of_forall_le
  intro result hresult
  simp only [bind_pure_comp, probEvent_map, Function.comp_def]
  apply sourcePrefixFinish_firstLane_probability_le_acceptance_of_noAcceptedEncoding
  change ¬HasAcceptedEncoding key.publicKey.parameter result.2.counts.cache
  rw [hparameter]
  exact hbudget.noAcceptedEncoding_after_last_nonencoding hlast hcache hinput result hresult

/-- info: 'XmssSecurity.Deciding.lastNonencodingSource_acceptedPrefix_probability_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lastNonencodingSource_acceptedPrefix_probability_eq_zero

/-- info: 'XmssSecurity.Deciding.lastNonencodingSource_firstLane_probability_le_acceptance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lastNonencodingSource_firstLane_probability_le_acceptance

end XmssSecurity.Deciding
