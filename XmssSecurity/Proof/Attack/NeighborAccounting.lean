import XmssSecurity.Proof.Attack.NeighborBudget
import XmssSecurity.Proof.Modes.Keygen
import XmssSecurity.Proof.Modes.Projection
import XmssSecurity.Proof.Modes.AllHashes

/-! Accounting for all hashes and the one signing request of the neighboring-signature attack. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.Attack

open SUFCMA

attribute [local irreducible] sampleMasterSeed

theorem countHashQueries_support_bound {α : Type} (computation : OracleComp OracleWorld α)
    (bound : ℕ) (hbound : computation.IsQueryBoundP IsHashQuery bound)
    (result : α × ℕ) (hresult : result ∈ support (countHashQueries computation)) : result.2 ≤ bound := by
  induction computation using OracleComp.inductionOn generalizing bound result with
  | pure value =>
      simp only [countHashQueries_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact Nat.zero_le _
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      rw [countHashQueries_query_bind, mem_support_bind_iff] at hresult
      obtain ⟨answer, _, hrest⟩ := hresult
      simp only [bind_pure_comp, support_map, Set.mem_image] at hrest
      obtain ⟨tail, htail, rfl⟩ := hrest
      have htailBound := ih answer _ (hbound.2 answer) tail htail
      rcases input with uniformInput | hashInput
      · simpa [IsHashQuery] using htailBound
      · simp [IsHashQuery] at htailBound hbound ⊢
        omega

theorem liftWorldToAdversary_counted {Key α : Type} (scheme : EpochBasedSignature OracleWorld PublicKey Key Message Signature lifetime) (secretKey : Key)
    (requestCost : ℕ) (computation : OracleComp OracleWorld α) :
    (simulateQ
      ((QueryImpl.ofLift OracleWorld (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld))).withAddCost
          (RandomOracleModel.hashCost HashInput HashOutput) +
        SUFCMA.signingOracleCounted (RandomOracleModel.hashCost HashInput HashOutput) requestCost scheme secretKey)
      (liftWorldToAdversary computation)).run.run =
      (fun result : α × ℕ => ((result.1, Multiplicative.ofAdd result.2), ([] : QueryLog SigningSpec))) <$>
        countHashQueries computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [liftWorldToAdversary, countHashQueries_pure]
  | query_bind input next ih =>
      simp only [liftWorldToAdversary, simulateQ_bind, simulateQ_spec_query] at ih ⊢
      rw [countHashQueries_query_bind]
      simp only [QueryImpl.add_apply_inl, QueryImpl.withAddCost_apply, QueryImpl.ofLift_apply,
        WriterT.run_bind, WriterT.run_monadLift, WriterT.run_map', Modes.run_liftM_of_liftM',
        AddWriterT.run_addTell, pure_bind, bind_map_left, map_bind, map_pure, Functor.map_map,
        ih, mul_one]
      apply bind_congr
      intro answer
      rw [map_eq_bind_pure_comp]
      apply bind_congr
      intro result
      cases input <;> rfl

theorem signingOracleCounted_run {Key : Type} (scheme : EpochBasedSignature OracleWorld PublicKey Key Message Signature lifetime) (secretKey : Key)
    (requestCost : ℕ) (request : XmssSecurity.SignRequest) :
    (SUFCMA.signingOracleCounted (RandomOracleModel.hashCost HashInput HashOutput)
      requestCost scheme secretKey request).run.run =
      (fun result : Option Signature × ℕ =>
        ((result.1, Multiplicative.ofAdd (requestCost + result.2)), [⟨request, result.1⟩])) <$>
        countHashQueries (scheme.sign secretKey request.epoch request.message) := by
  simp only [SUFCMA.signingOracleCounted, Modes.charge_hashCost_eq_countHashQueries,
    WriterT.run_bind, WriterT.run_monadLift, Modes.run_run_liftM, WriterT.run_pure,
    WriterT.run_tell, AddWriterT.run_addTell, pure_bind, bind_map_left, map_bind,
    map_pure, mul_one, one_mul]
  rfl

theorem neighborMain_counted {Key : Type} (scheme : EpochBasedSignature OracleWorld PublicKey Key Message Signature lifetime) (secretKey : Key) (publicKey : PublicKey) :
    (simulateQ
      ((QueryImpl.ofLift OracleWorld (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld))).withAddCost
          (RandomOracleModel.hashCost HashInput HashOutput) +
        SUFCMA.signingOracleCounted (RandomOracleModel.hashCost HashInput HashOutput) 1 scheme secretKey)
      (neighborMain publicKey)).run.run = (do
      let signed ← countHashQueries (scheme.sign secretKey neighborRequest.epoch neighborRequest.message)
      let forged ← countHashQueries (neighborAfterSigning publicKey signed.1)
      return ((neighborForgery forged.1, Multiplicative.ofAdd (1 + signed.2 + forged.2)),
        [⟨neighborRequest, signed.1⟩])) := by
  unfold neighborMain
  simp only [bind_pure_comp, simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inr,
    WriterT.run_bind, simulateQ_map, WriterT.run_map',
    liftWorldToAdversary_counted, Functor.map_map, Prod.map_apply, id_eq, List.append_nil]
  rw [signingOracleCounted_run scheme secretKey 1 neighborRequest]
  simp only [bind_map_left]
  rfl

theorem neighbor_gameCounted_everything :
    SUFCMA.gameCounted CountingMode.everything (RandomOracleModel.hashCost HashInput HashOutput)
      xmss neighborSufCmaAdversary = (do
      let keyResult ← countHashQueries xmss.keygen
      let signed ← countHashQueries (xmss.sign keyResult.1.2 neighborRequest.epoch neighborRequest.message)
      let forged ← countHashQueries (neighborAfterSigning keyResult.1.1 signed.1)
      let verified ← countHashQueries (xmss.verify keyResult.1.1 neighborRequest.epoch neighborMessage forged.1)
      return (verified.1, keyResult.2 + (1 + signed.2 + forged.2) + verified.2)) := by
  unfold SUFCMA.gameCounted
  simp only [CountingMode.everything, costIf, if_true, Modes.charge_hashCost_eq_countHashQueries]
  have hmain := fun (publicKey : PublicKey) (secretKey : Seeded.SecretKey) =>
    neighborMain_counted xmss secretKey publicKey
  simp only [neighborSufCmaAdversary, hmain, bind_assoc, pure_bind, neighbor_transcript_fresh, not_false_eq_true,
    show ∀ answer : Option Signature, SigningTranscript.Valid [⟨neighborRequest, answer⟩] from
      fun _ => by simp [SUFCMA.SigningTranscript.Valid], and_true, decide_true, Bool.true_and]
  rfl

theorem neighbor_counted_support_bound (result : Bool × ℕ)
    (hresult : result ∈ support (SUFCMA.gameCounted CountingMode.everything
      (RandomOracleModel.hashCost HashInput HashOutput) xmss neighborSufCmaAdversary)) :
    result.2 ≤ neighborEverythingBudget := by
  rw [neighbor_gameCounted_everything] at hresult
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hresult
  obtain ⟨keyResult, hkey, signed, hsign, forged, hforged, verified, hverified, rfl⟩ := hresult
  have hkeyBound := countHashQueries_support_bound _ _ xmss_keygen_queryBound keyResult hkey
  have hsignBound := countHashQueries_support_bound _ _
    (xmss_sign_queryBound keyResult.1.2 neighborRequest.epoch neighborRequest.message) signed hsign
  have hforgedBound := countHashQueries_support_bound _ neighborDirectBudget (by
    apply (OracleComp.isQueryBoundP_congr_pred (p := Seeded.hashBad (fun _ => True))
      (p' := IsHashQuery) (fun input => by cases input <;> simp [Seeded.hashBad, IsHashQuery])).mp
    exact neighborAfterSigning_queryBound keyResult.1.1 signed.1) forged hforged
  have hverifier : (xmss.verify keyResult.1.1 neighborRequest.epoch neighborMessage forged.1).IsQueryBoundP
      IsHashQuery Direct.verifierQueryBound := by
    change (liftComp (Concrete.verify keyResult.1.1 neighborRequest.epoch neighborMessage forged.1 :
      OracleComp HashSpec Bool) OracleWorld).IsQueryBoundP _ _
    exact OracleComp.IsQueryBoundP.liftComp_subSpec (p := fun _ => True) (q := IsHashQuery)
      (fun input => by change True ↔ IsHashQuery (.inr input); simp [IsHashQuery])
      (Direct.verify_isQueryBoundP _ _ _ _)
  have hverifiedBound := countHashQueries_support_bound _ _ hverifier verified hverified
  have htotal := neighbor_total_budget_le
  dsimp only at hkeyBound hsignBound hforgedBound hverifiedBound ⊢
  omega

theorem neighbor_everything_queryBound :
    (SUFCMA.notion CountingMode.everything).HasQueryBound xmss neighborSufCmaAdversary neighborEverythingBudget := by
  intro result hresult
  apply neighbor_counted_support_bound result
  exact support_simulateQ_run'_subset romImpl _ ∅ hresult

theorem neighbor_everything_advantage :
    (SUFCMA.notion CountingMode.everything).advantage xmss neighborSufCmaAdversary =
      forgeAdvantage Seeded.scheme neighborAdversary := by
  rw [Modes.advantage_eq_of_mode _ CountingMode.direct,
    Modes.notion_direct_advantage_eq, Security.notionDirect_advantage_eq]
  rfl

theorem neighbor_everything_attack : ¬(SUFCMA.notion SUFCMA.CountingMode.everything).HasClassicalSecurityBits xmss (127 + 1) := by
  intro hsecure
  have hbound := hsecure neighborEverythingBudget (by norm_num [neighborEverythingBudget])
    neighborSufCmaAdversary neighbor_everything_queryBound
  rw [neighbor_everything_advantage, neighborEverythingBudget_ratio] at hbound
  exact (not_lt_of_ge hbound) neighbor_seeded_advantage_exceeds_eightyone_256ths

/-- info: 'XmssSecurity.Attack.neighbor_everything_queryBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms neighbor_everything_queryBound

/-- info: 'XmssSecurity.Attack.neighbor_everything_attack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms neighbor_everything_attack

end XmssSecurity.Attack
