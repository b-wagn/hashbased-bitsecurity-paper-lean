import XmssSecurity.Proof.Checksum.Attack.ChainMutationSeeded
import XmssSecurity.Proof.Checksum.Attack.NeighborAccounting

/-! The mutation adversary when the signer's hash calls are charged.

Its single signing request costs the two hash calls of the signer (the randomizer and the
encoding), so it is charged at most `2` when the signer is charged, and at most `3` when the
request itself is charged too. Its advantage above `2^-123` therefore refutes `124` bits in the
first mode and `125` bits in the second. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.Checksum.Attack

open SUFCMA

attribute [local irreducible] sampleMasterSeed

theorem liftPrivateSamples_counted {Key α : Type}
    (scheme : EpochBasedSignature OracleWorld PublicKey Key Message Signature lifetime)
    (secretKey : Key) (requestCost : ℕ) (computation : ProbComp α) :
    (simulateQ
      ((QueryImpl.ofLift OracleWorld (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld))).withAddCost
          (RandomOracleModel.hashCost HashInput HashOutput) +
        SUFCMA.signingOracleCounted (RandomOracleModel.hashCost HashInput HashOutput) requestCost scheme secretKey)
      (liftPrivateSamples computation)).run.run =
      (fun result : α => ((result, Multiplicative.ofAdd 0), ([] : QueryLog SigningSpec))) <$>
        worldPrivateSamples computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [liftPrivateSamples, worldPrivateSamples]
  | query_bind input next ih =>
      simp only [liftPrivateSamples, worldPrivateSamples, simulateQ_bind, simulateQ_spec_query]
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
    OracleComp (OracleWorld + SigningSpec) Forgery := do
  let answer ← liftM ((OracleWorld + SigningSpec).query (.inr mutationRequest))
  let choice ← liftPrivateSamples choices
  return chainMutationForgery answer choice

theorem chainMutationMain_eq_of : chainMutationMain = chainMutationMainOf mutationChoice := rfl

theorem chainMutationMainOf_counted {Key : Type}
    (scheme : EpochBasedSignature OracleWorld PublicKey Key Message Signature lifetime)
    (secretKey : Key) (requestCost : ℕ) (choices : ProbComp (ChainIndex × Digest)) :
    (simulateQ
      ((QueryImpl.ofLift OracleWorld (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld))).withAddCost
          (RandomOracleModel.hashCost HashInput HashOutput) +
        SUFCMA.signingOracleCounted (RandomOracleModel.hashCost HashInput HashOutput) requestCost scheme secretKey)
      (chainMutationMainOf choices)).run.run = (do
      let signed ← countHashQueries (scheme.sign secretKey mutationRequest.epoch mutationRequest.message)
      let choice ← worldPrivateSamples choices
      return ((chainMutationForgery signed.1 choice, Multiplicative.ofAdd (requestCost + signed.2)),
        [⟨mutationRequest, signed.1⟩])) := by
  unfold chainMutationMainOf
  simp only [bind_pure_comp, simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inr,
    WriterT.run_bind, simulateQ_map, WriterT.run_map', liftPrivateSamples_counted,
    Functor.map_map, Prod.map_apply, id_eq, List.append_nil]
  rw [signingOracleCounted_run scheme secretKey requestCost mutationRequest]
  simp only [bind_map_left]
  rfl

/-- In a mode charging the signer but neither key generation nor verification, the mutation
adversary is charged its request (if requests are charged) and the signer's hash calls. -/
theorem chainMutation_signer_counted_support_bound (requests : Bool) (result : Bool × ℕ)
    (hresult : result ∈ support (SUFCMA.gameCounted ⟨false, true, false, requests⟩
      (RandomOracleModel.hashCost HashInput HashOutput) xmss chainMutationSufCmaAdversary)) :
    result.2 ≤ (if requests then 1 else 0) + 2 := by
  unfold SUFCMA.gameCounted at hresult
  simp only [costIf, Bool.false_eq_true, if_false, if_true, Modes.charge_zero] at hresult
  have hmain := fun (secretKey : Seeded.SecretKey) =>
    chainMutationMainOf_counted xmss secretKey (if requests then 1 else 0) mutationChoice
  simp only [show chainMutationSufCmaAdversary.main = fun _ => chainMutationMainOf mutationChoice
    from rfl, hmain] at hresult
  simp only [bind_map_left, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff, bind_assoc, pure_bind] at hresult
  obtain ⟨keyResult, _, signed, hsign, choice, _, verified, _, rfl⟩ := hresult
  have hsignBound := countHashQueries_support_bound _ _
    (xmss_sign_queryBound keyResult.2 mutationRequest.epoch mutationRequest.message) signed hsign
  simp only [signingAttemptLimit] at hsignBound
  have htoAdd : Multiplicative.toAdd (Multiplicative.ofAdd ((if requests then 1 else 0) + signed.2)) =
      (if requests then 1 else 0) + signed.2 := rfl
  simp only [htoAdd, zero_add, add_zero]
  omega

theorem chainMutation_signer_queryBound (requests : Bool) :
    (SUFCMA.notion ⟨false, true, false, requests⟩).HasQueryBound xmss
      chainMutationSufCmaAdversary ((if requests then 1 else 0) + 2) := by
  intro result hresult
  apply chainMutation_signer_counted_support_bound requests result
  exact support_simulateQ_run'_subset romImpl _ ∅ hresult

theorem chainMutation_signer_advantage (mode : CountingMode) :
    (SUFCMA.notion mode).advantage xmss chainMutationSufCmaAdversary =
      forgeAdvantage Seeded.scheme chainMutationAdversary := by
  rw [Modes.advantage_eq_of_mode _ SUFCMA.CountingMode.direct,
    Modes.notion_direct_advantage_eq, Security.notionDirect_advantage_eq]
  rfl

/-- Charging the signer, the mutation adversary is charged `2` and refutes `124` bits. -/
theorem chainMutation_signer_attack :
    ¬(SUFCMA.notion ⟨false, true, false, false⟩).HasClassicalSecurityBits xmss (123 + 1) := by
  intro hsecure
  have hbound := hsecure 2 (by norm_num) chainMutationSufCmaAdversary
    (by simpa using chainMutation_signer_queryBound false)
  rw [chainMutation_signer_advantage] at hbound
  apply (not_lt_of_ge hbound)
  refine lt_of_eq_of_lt ?_ chainMutation_seeded_advantage_exceeds_123
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_div]

/-- Charging the signer and the requests, the mutation adversary is charged `3` and refutes
`125` bits. -/
theorem chainMutation_signerRequests_attack :
    ¬(SUFCMA.notion ⟨false, true, false, true⟩).HasClassicalSecurityBits xmss (124 + 1) := by
  intro hsecure
  have hbound := hsecure 3 (by norm_num) chainMutationSufCmaAdversary
    (by simpa using chainMutation_signer_queryBound true)
  rw [chainMutation_signer_advantage] at hbound
  apply (not_lt_of_ge hbound)
  refine lt_of_le_of_lt ?_ chainMutation_seeded_advantage_exceeds_123
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_div]

/-- info: 'XmssSecurity.Checksum.Attack.chainMutation_signer_attack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms chainMutation_signer_attack

/-- info: 'XmssSecurity.Checksum.Attack.chainMutation_signerRequests_attack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms chainMutation_signerRequests_attack

end XmssSecurity.Checksum.Attack
