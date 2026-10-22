import Xmss.Proof.Checksum.Attack.ChainMutationSeeded
import Xmss.Proof.Checksum.Attack.NeighborAccounting
import Xmss.Proof.Checksum.Code
import Xmss.Proof.Checksum.EncodingProbability

/-! The mutation adversary when the signer's hash calls are charged.

Its single signing request costs the two hash calls of the signer (the randomizer and the
encoding), so it is charged at most `2` when the signer is charged, and at most `3` when the
request itself is charged too. Its advantage above `2^-123` therefore refutes `124` bits in the
first mode and `125` bits in the second. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace Xmss.Checksum.Attack

open Unforgeability SUFCMA

attribute [local irreducible] Generic.sampleMasterSeed

theorem liftPrivateSamples_counted {Key α : Type}
    (scheme : EpochBasedSignature OracleWorld PublicKey Key Message Generic.Signature lifetime)
    (secretKey : Key) (requestCost : ℕ) (computation : ProbComp α) :
    (simulateQ
      ((QueryImpl.ofLift OracleWorld (WriterT (QueryLog Generic.SigningSpec) (OracleComp OracleWorld))).withAddCost
          (RandomOracleModel.hashCost HashInput Digest) +
        Unforgeability.signingOracleCounted (RandomOracleModel.hashCost HashInput Digest) requestCost scheme secretKey)
      (Generic.Attack.liftPrivateSamples computation)).run.run =
      (fun result : α => ((result, Multiplicative.ofAdd 0), ([] : QueryLog Generic.SigningSpec))) <$>
        worldPrivateSamples computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [Generic.Attack.liftPrivateSamples, worldPrivateSamples]
  | query_bind input next ih =>
      simp only [Generic.Attack.liftPrivateSamples, worldPrivateSamples, simulateQ_bind, simulateQ_spec_query]
        at ih ⊢
      simp only [QueryImpl.add_apply_inl, QueryImpl.withAddCost_apply, QueryImpl.ofLift_apply,
        WriterT.run_bind, WriterT.run_monadLift, WriterT.run_map', Modes.run_liftM_of_liftM',
        AddWriterT.run_addTell, pure_bind, bind_map_left, map_bind, Functor.map_map,
        ih, mul_one]
      apply bind_congr
      intro answer
      simp [RandomOracleModel.hashCost]

/-- The mutation adversary with an arbitrary private choice of chain and value. Stating the
accounting for an arbitrary sampler keeps the kernel from unfolding the uniform sampler. -/
noncomputable def chainMutationMainOf (choices : ProbComp (ChainIndex × Digest)) :
    OracleComp (OracleWorld + Generic.SigningSpec) Generic.Forgery := do
  let answer ← liftM ((OracleWorld + Generic.SigningSpec).query (.inr Generic.Attack.mutationRequest))
  let choice ← Generic.Attack.liftPrivateSamples choices
  return Generic.Attack.chainMutationForgery answer choice

theorem chainMutationMainOf_counted {Key : Type}
    (scheme : EpochBasedSignature OracleWorld PublicKey Key Message Generic.Signature lifetime)
    (secretKey : Key) (requestCost : ℕ) (choices : ProbComp (ChainIndex × Digest)) :
    (simulateQ
      ((QueryImpl.ofLift OracleWorld (WriterT (QueryLog Generic.SigningSpec) (OracleComp OracleWorld))).withAddCost
          (RandomOracleModel.hashCost HashInput Digest) +
        Unforgeability.signingOracleCounted (RandomOracleModel.hashCost HashInput Digest) requestCost scheme secretKey)
      (chainMutationMainOf choices)).run.run = (do
      let signed ← Generic.countHashQueries (scheme.sign secretKey Generic.Attack.mutationRequest.epoch Generic.Attack.mutationRequest.message)
      let choice ← worldPrivateSamples choices
      return ((Generic.Attack.chainMutationForgery signed.1 choice, Multiplicative.ofAdd (requestCost + signed.2)),
        [⟨Generic.Attack.mutationRequest, signed.1⟩])) := by
  unfold chainMutationMainOf
  simp only [bind_pure_comp, simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inr,
    WriterT.run_bind, simulateQ_map, WriterT.run_map', liftPrivateSamples_counted,
    Functor.map_map, Prod.map_apply, id_eq, List.append_nil]
  rw [signingOracleCounted_run scheme secretKey requestCost Generic.Attack.mutationRequest]
  simp only [bind_map_left]
  rfl

/-- In a mode charging the signer but neither key generation nor verification, the mutation
adversary is charged its request (if requests are charged) and the signer's hash calls. -/
theorem chainMutation_signer_counted_support_bound (requests : Bool) (result : Bool × ℕ)
    (hresult : result ∈ support (SUFCMA.gameCounted ⟨false, true, false, requests⟩
      (RandomOracleModel.hashCost HashInput Digest) Generic.xmss Generic.Attack.chainMutationSufCmaAdversary)) :
    result.2 ≤ (if requests then 1 else 0) + 2 := by
  unfold SUFCMA.gameCounted at hresult
  simp only [costIf, Bool.false_eq_true, if_false, if_true, Modes.charge_zero] at hresult
  have hmain := fun (secretKey : Generic.Seeded.SecretKey) =>
    chainMutationMainOf_counted Generic.xmss secretKey (if requests then 1 else 0) Generic.Attack.mutationChoice
  simp only [show Generic.Attack.chainMutationSufCmaAdversary.main = fun _ => chainMutationMainOf Generic.Attack.mutationChoice
    from rfl, hmain] at hresult
  simp only [bind_map_left, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff, bind_assoc, pure_bind] at hresult
  obtain ⟨keyResult, _, signed, hsign, choice, _, verified, _, rfl⟩ := hresult
  have hsignBound := countHashQueries_support_bound _ _
    (xmss_sign_queryBound keyResult.2 Generic.Attack.mutationRequest.epoch Generic.Attack.mutationRequest.message) signed hsign
  simp only [signingAttemptLimit] at hsignBound
  have htoAdd : Multiplicative.toAdd (Multiplicative.ofAdd ((if requests then 1 else 0) + signed.2)) =
      (if requests then 1 else 0) + signed.2 := rfl
  simp only [htoAdd, zero_add, add_zero]
  omega

theorem chainMutation_signer_queryBound (requests : Bool) :
    (SUFCMA.notion ⟨false, true, false, requests⟩).HasQueryBound Generic.xmss
      Generic.Attack.chainMutationSufCmaAdversary ((if requests then 1 else 0) + 2) := by
  intro result hresult
  apply chainMutation_signer_counted_support_bound requests result
  exact support_simulateQ_run'_subset Generic.romImpl _ ∅ hresult

theorem chainMutation_signer_advantage (mode : CountingMode) :
    (SUFCMA.notion mode).advantage Generic.xmss Generic.Attack.chainMutationSufCmaAdversary =
      Generic.forgeAdvantage Generic.Seeded.scheme Generic.Attack.chainMutationAdversary := by
  rw [Modes.advantage_eq_of_mode _ Unforgeability.CountingMode.direct,
    Modes.notion_direct_advantage_eq, Generic.AdversaryBridge.notionDirect_advantage_eq]
  rfl

/-- Charging the signer, the mutation adversary is charged `2` and refutes `124` bits. -/
theorem chainMutation_signer_attack :
    ¬(SUFCMA.notion ⟨false, true, false, false⟩).HasClassicalSecurityBits Generic.xmss (123 + 1) := by
  intro hsecure
  have hbound := hsecure 2 (by norm_num) Generic.Attack.chainMutationSufCmaAdversary
    (by simpa using chainMutation_signer_queryBound false)
  rw [chainMutation_signer_advantage] at hbound
  apply (not_lt_of_ge hbound)
  refine lt_of_eq_of_lt ?_ chainMutation_seeded_advantage_exceeds_123
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_div]

/-- Charging the signer and the requests, the mutation adversary is charged `3` and refutes
`125` bits. -/
theorem chainMutation_signerRequests_attack :
    ¬(SUFCMA.notion ⟨false, true, false, true⟩).HasClassicalSecurityBits Generic.xmss (124 + 1) := by
  intro hsecure
  have hbound := hsecure 3 (by norm_num) Generic.Attack.chainMutationSufCmaAdversary
    (by simpa using chainMutation_signer_queryBound true)
  rw [chainMutation_signer_advantage] at hbound
  apply (not_lt_of_ge hbound)
  refine lt_of_le_of_lt ?_ chainMutation_seeded_advantage_exceeds_123
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_div]

/-- info: 'Xmss.Checksum.Attack.chainMutation_signer_attack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms chainMutation_signer_attack

/-- info: 'Xmss.Checksum.Attack.chainMutation_signerRequests_attack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms chainMutation_signerRequests_attack

end Xmss.Checksum.Attack
