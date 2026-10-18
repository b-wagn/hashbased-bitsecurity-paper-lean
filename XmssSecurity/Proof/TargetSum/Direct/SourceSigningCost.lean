import XmssSecurity.Proof.TargetSum.Direct.SourceBudgetExhaustion
import XmssSecurity.Proof.TargetSum.Deterministic.SignerCost
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Every reference signing request performs at least one encoding hash, including
failed requests and cache hits. Its source charge is therefore at least two. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum

theorem precomputedSignBoundedAttempts_count_positive (attempts : Nat) (secretKey : Generic.SecretKey)
    (leaf : LeafIndex) (message : Message) (cache : QueryCache HashSpec)
    (result : (Option Generic.Signature × Nat) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ romImpl (countHashQueries
      (Concrete.precomputedSignBoundedAttempts (attempts + 1) secretKey leaf message))).run cache)) :
    1 ≤ result.1.2 := by
  rw [Concrete.precomputedSignBoundedAttempts, countHashQueries_bind] at hresult
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hresult
  obtain ⟨sample, _hsample, tail, htail, rfl⟩ := hresult
  simp only [Concrete.precomputedSignAttempt_lift_hash_eq_world, countHashQueries_bind,
    countHashQueries_precomputedSignAttempt, simulateQ_bind, StateT.run_bind,
    simulateQ_map, StateT.run_map, simulateQ_pure, StateT.run_pure,
    mem_support_bind_iff, support_map, support_pure, Set.mem_singleton_iff] at htail
  obtain ⟨head, ⟨attempt, _hattempt, rfl⟩, rest, _hrest, rfl⟩ := htail
  dsimp only
  omega

theorem precomputedCappedSign_count_positive (secretKey : Generic.SecretKey)
    (leaf : LeafIndex) (message : Message) (cache : QueryCache HashSpec)
    (result : (Option Generic.Signature × Nat) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ romImpl (countHashQueries
      (Concrete.precomputedCappedSign secretKey leaf message))).run cache)) :
    1 ≤ result.1.2 := by
  unfold Concrete.precomputedCappedSign at hresult
  have hattempts : signingAttemptLimit = (signingAttemptLimit - 1) + 1 := by
    norm_num [signingAttemptLimit]
  rw [code_signingAttemptLimit, hattempts] at hresult
  exact precomputedSignBoundedAttempts_count_positive _ secretKey leaf message cache result hresult

namespace CappedChain

open Seeded

theorem countedSourceImpl_signing_charge_growth (secretKey : Generic.SecretKey) (request : SignRequest)
    (state : CountedSourceState) (result : Option Generic.Signature × CountedSourceState)
    (hresult : result ∈ support ((countedSourceImpl secretKey (.inr request)).run state)) :
    state.charge + 2 ≤ result.2.charge := by
  simp only [countedSourceImpl, StateT.run, support_map] at hresult
  obtain ⟨handled, hhandled, rfl⟩ := hresult
  simp only [referencePhaseCountsImpl, phaseCountsImpl, StateT.run, support_map] at hhandled
  obtain ⟨sample, hsample, rfl⟩ := hhandled
  have hpositive := precomputedCappedSign_count_positive secretKey request.epoch request.message
    state.counts.cache sample hsample
  change state.counts.direct + 2 * state.counts.signing + 2 ≤
    state.counts.direct + 2 * (state.counts.signing + sample.1.2)
  omega

theorem CountedSourceBudget.signing_room {α : Type} {secretKey : Generic.SecretKey} {limit : Nat}
    {request : SignRequest} {next : Option Generic.Signature → OracleComp (OracleWorld + SigningSpec) α}
    {state : CountedSourceState}
    (hbudget : CountedSourceBudget secretKey limit
      (liftM ((OracleWorld + SigningSpec).query (.inr request)) >>= next) state) :
    state.charge + 2 ≤ limit := by
  obtain ⟨head, hhead⟩ := probComp_support_nonempty ((countedSourceImpl secretKey (.inr request)).run state)
  exact (countedSourceImpl_signing_charge_growth secretKey request state head hhead).trans
    (hbudget.query_step head hhead).1

theorem CountedSourceBudget.direct_hash_room {α : Type} {secretKey : Generic.SecretKey} {limit : Nat}
    {input : HashInput} {next : HashOutput → OracleComp (OracleWorld + SigningSpec) α}
    {state : CountedSourceState}
    (hbudget : CountedSourceBudget secretKey limit
      (liftM ((OracleWorld + SigningSpec).query (.inl (.inr input))) >>= next) state) :
    state.charge + 1 ≤ limit := by
  obtain ⟨head, hhead⟩ := probComp_support_nonempty
    ((countedSourceImpl secretKey (.inl (.inr input))).run state)
  have hcharge := (hbudget.query_step head hhead).1
  have hdirect := countedSourceImpl_direct_eq secretKey (.inl (.inr input)) state head hhead
  have hmono := countedSourceImpl_counts_mono secretKey (.inl (.inr input)) state head hhead
  change head.2.counts.direct = state.counts.direct + 1 at hdirect
  unfold CountedSourceState.charge at hcharge ⊢
  omega

/-- info: 'XmssSecurity.TargetSum.CappedChain.CountedSourceBudget.signing_room' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CountedSourceBudget.signing_room

end CappedChain
end XmssSecurity.TargetSum
