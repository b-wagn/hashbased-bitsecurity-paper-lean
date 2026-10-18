import XmssSecurity.Proof.Checksum.Attack.ChainMutationSigner
import XmssSecurity.Proof.Checksum.Code
import XmssSecurity.Proof.Checksum.EncodingProbability

/-! Adversaries that make one signing request at `mutationRequest`, sample privately, and output a
forgery computed from the answer and the samples, with no hash query of their own.

The accounting of the mutation adversary (`ChainMutationSigner.lean`) holds for every such
adversary: it is charged `1` when the requests are charged, and the two hash calls of the signer
when the signer is charged. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.Checksum.Attack

open SUFCMA

attribute [local irreducible] Generic.sampleMasterSeed

theorem liftPrivateSamples_counted_zero {Key α : Type}
    (scheme : EpochBasedSignature OracleWorld PublicKey Key Message Generic.Signature lifetime)
    (secretKey : Key) (requestCost : ℕ) (computation : ProbComp α) :
    (simulateQ
      ((QueryImpl.ofLift OracleWorld (WriterT (QueryLog Generic.SigningSpec) (OracleComp OracleWorld))).withAddCost
          (RandomOracleModel.hashCost HashInput Digest) +
        SUFCMA.signingOracleCounted (fun _ => 0) requestCost scheme secretKey)
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

/-- Request `mutationRequest`, sample `choices` privately, and forge `finish answer choice`. -/
noncomputable def oneRequestMain (finish : Option Generic.Signature → ChainIndex × Digest → Generic.Forgery)
    (choices : ProbComp (ChainIndex × Digest)) : OracleComp (OracleWorld + Generic.SigningSpec) Generic.Forgery := do
  let answer ← liftM ((OracleWorld + Generic.SigningSpec).query (.inr Generic.Attack.mutationRequest))
  let choice ← Generic.Attack.liftPrivateSamples choices
  return finish answer choice

noncomputable def oneRequestAdversary (finish : Option Generic.Signature → ChainIndex × Digest → Generic.Forgery) :
    Generic.Adversary := ⟨fun _ => oneRequestMain finish Generic.Attack.mutationChoice⟩

noncomputable def oneRequestSufCmaAdversary
    (finish : Option Generic.Signature → ChainIndex × Digest → Generic.Forgery) :
    SUFCMA.Adversary OracleWorld PublicKey Message Generic.Signature lifetime :=
  ⟨fun _ => oneRequestMain finish Generic.Attack.mutationChoice⟩

theorem oneRequestMain_counted {Key : Type}
    (scheme : EpochBasedSignature OracleWorld PublicKey Key Message Generic.Signature lifetime)
    (secretKey : Key) (requestCost : ℕ)
    (finish : Option Generic.Signature → ChainIndex × Digest → Generic.Forgery)
    (choices : ProbComp (ChainIndex × Digest)) :
    (simulateQ
      ((QueryImpl.ofLift OracleWorld (WriterT (QueryLog Generic.SigningSpec) (OracleComp OracleWorld))).withAddCost
          (RandomOracleModel.hashCost HashInput Digest) +
        SUFCMA.signingOracleCounted (RandomOracleModel.hashCost HashInput Digest) requestCost scheme secretKey)
      (oneRequestMain finish choices)).run.run = (do
      let signed ← Generic.countHashQueries (scheme.sign secretKey Generic.Attack.mutationRequest.epoch Generic.Attack.mutationRequest.message)
      let choice ← worldPrivateSamples choices
      return ((finish signed.1 choice, Multiplicative.ofAdd (requestCost + signed.2)),
        [⟨Generic.Attack.mutationRequest, signed.1⟩])) := by
  unfold oneRequestMain
  simp only [bind_pure_comp, simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inr,
    WriterT.run_bind, simulateQ_map, WriterT.run_map', liftPrivateSamples_counted,
    Functor.map_map, Prod.map_apply, id_eq, List.append_nil]
  rw [signingOracleCounted_run scheme secretKey requestCost Generic.Attack.mutationRequest]
  simp only [bind_map_left]
  rfl

theorem signingOracleCounted_zero_run {Key : Type}
    (scheme : EpochBasedSignature OracleWorld PublicKey Key Message Generic.Signature lifetime)
    (secretKey : Key) (requestCost : ℕ) (request : Generic.SignRequest) :
    (SUFCMA.signingOracleCounted (fun _ => 0) requestCost scheme secretKey request).run.run =
      (fun answer : Option Generic.Signature =>
        ((answer, Multiplicative.ofAdd requestCost), [⟨request, answer⟩])) <$>
        scheme.sign secretKey request.epoch request.message := by
  simp only [SUFCMA.signingOracleCounted, Modes.charge_zero,
    WriterT.run_bind, WriterT.run_monadLift, Modes.run_run_liftM, WriterT.run_pure,
    WriterT.run_tell, AddWriterT.run_addTell, pure_bind, bind_map_left, map_bind,
    map_pure, mul_one, one_mul, add_zero]
  rfl

theorem oneRequestMain_counted_zero {Key : Type}
    (scheme : EpochBasedSignature OracleWorld PublicKey Key Message Generic.Signature lifetime)
    (secretKey : Key) (requestCost : ℕ)
    (finish : Option Generic.Signature → ChainIndex × Digest → Generic.Forgery)
    (choices : ProbComp (ChainIndex × Digest)) :
    (simulateQ
      ((QueryImpl.ofLift OracleWorld (WriterT (QueryLog Generic.SigningSpec) (OracleComp OracleWorld))).withAddCost
          (RandomOracleModel.hashCost HashInput Digest) +
        SUFCMA.signingOracleCounted (fun _ => 0) requestCost scheme secretKey)
      (oneRequestMain finish choices)).run.run = (do
      let answer ← scheme.sign secretKey Generic.Attack.mutationRequest.epoch Generic.Attack.mutationRequest.message
      let choice ← worldPrivateSamples choices
      return ((finish answer choice, Multiplicative.ofAdd requestCost),
        [⟨Generic.Attack.mutationRequest, answer⟩])) := by
  unfold oneRequestMain
  simp only [bind_pure_comp, simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inr,
    WriterT.run_bind, simulateQ_map, WriterT.run_map', liftPrivateSamples_counted_zero,
    Functor.map_map, Prod.map_apply, id_eq, List.append_nil]
  rw [signingOracleCounted_zero_run scheme secretKey requestCost Generic.Attack.mutationRequest]
  simp only [bind_map_left]
  rfl

/-- The charge of a one-request adversary in a mode charging neither key generation nor
verification: its request, if requests are charged, and the signer's hash calls, if the signer is
charged. -/
theorem oneRequest_counted_support_bound
    (finish : Option Generic.Signature → ChainIndex × Digest → Generic.Forgery) (signer requests : Bool)
    (result : Bool × ℕ)
    (hresult : result ∈ support (SUFCMA.gameCounted ⟨false, signer, false, requests⟩
      (RandomOracleModel.hashCost HashInput Digest) Generic.xmss (oneRequestSufCmaAdversary finish))) :
    result.2 ≤ (if requests then 1 else 0) + (if signer then 2 else 0) := by
  unfold SUFCMA.gameCounted at hresult
  cases signer
  · -- The signer's hash calls are not charged.
    simp only [costIf, Bool.false_eq_true, if_false, Modes.charge_zero] at hresult
    have hmain := fun (secretKey : Generic.Seeded.SecretKey) =>
      oneRequestMain_counted_zero Generic.xmss secretKey (if requests then 1 else 0) finish Generic.Attack.mutationChoice
    simp only [show (oneRequestSufCmaAdversary finish).main =
      fun _ => oneRequestMain finish Generic.Attack.mutationChoice from rfl, hmain] at hresult
    simp only [bind_map_left, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff, bind_assoc, pure_bind] at hresult
    obtain ⟨keyResult, _, answer, _, choice, _, verified, _, rfl⟩ := hresult
    have htoAdd : Multiplicative.toAdd (Multiplicative.ofAdd (if requests then 1 else 0)) =
        (if requests then 1 else 0) := rfl
    cases requests <;> simp [htoAdd]
  · simp only [costIf, Bool.false_eq_true, if_false, if_true, Modes.charge_zero] at hresult
    have hmain := fun (secretKey : Generic.Seeded.SecretKey) =>
      oneRequestMain_counted Generic.xmss secretKey (if requests then 1 else 0) finish Generic.Attack.mutationChoice
    simp only [show (oneRequestSufCmaAdversary finish).main =
      fun _ => oneRequestMain finish Generic.Attack.mutationChoice from rfl, hmain] at hresult
    simp only [bind_map_left, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff, bind_assoc, pure_bind] at hresult
    obtain ⟨keyResult, _, signed, hsign, choice, _, verified, _, rfl⟩ := hresult
    have hsignBound := countHashQueries_support_bound _ _
      (xmss_sign_queryBound keyResult.2 Generic.Attack.mutationRequest.epoch Generic.Attack.mutationRequest.message) signed hsign
    simp only [signingAttemptLimit] at hsignBound
    have htoAdd : Multiplicative.toAdd (Multiplicative.ofAdd ((if requests then 1 else 0) + signed.2)) =
        (if requests then 1 else 0) + signed.2 := rfl
    simp only [htoAdd, zero_add, add_zero, if_true]
    omega

end XmssSecurity.Checksum.Attack
