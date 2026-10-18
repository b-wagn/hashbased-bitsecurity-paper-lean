import XmssSecurity.Proof.TargetSum.Main.Unforgeability
import XmssSecurity.Proof.TargetSum.EUFCMA.ReplayAccounting
import XmssSecurity.Proof.Common.RepeatedEpochs

/-!
# The classifications in the statement's games

The classifications of `Main/StrongUnforgeability.lean` and `Main/Unforgeability.lean` are for the
lossy games, in which a repeated epoch loses. This file transfers them to the statement's games,
in which a repeated epoch is answered by `⊥` (`Proof/Common/RepeatedEpochs.lean`): the security
bounds transfer for every adversary, and every attack makes a single signing request, so it has
the same experiment in both games.
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.TargetSum.Attack

open SUFCMA

theorem liftPrivateSamples_noRequest {α : Type} (computation : ProbComp α) :
    (liftPrivateSamples computation).IsQueryBoundP
      (IsSigningQuery (spec := OracleWorld) (Msg := Message) (Sig := Signature) (L := lifetime)) 0 := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [liftPrivateSamples]
  | query_bind input next ih =>
      simp only [liftPrivateSamples, simulateQ_bind, simulateQ_spec_query] at ih ⊢
      refine (OracleComp.isQueryBoundP_query_bind_iff _ _ _ _).2
        ⟨Or.inl (by simp [IsSigningQuery]), fun answer => ?_⟩
      simpa [IsSigningQuery] using ih answer

theorem liftWorldToAdversary_noRequest {α : Type} (computation : OracleComp OracleWorld α) :
    (liftWorldToAdversary computation).IsQueryBoundP
      (IsSigningQuery (spec := OracleWorld) (Msg := Message) (Sig := Signature) (L := lifetime)) 0 :=
  liftWorldToAdversary_queryBound computation (fun _ => False) _ (fun _ => by simp [IsSigningQuery])
    0 (by induction computation using OracleComp.inductionOn <;> simp_all)

theorem oneRequest_of_request_then {β : Type} (request : SignRequest)
    (next : Option Signature → OracleComp (OracleWorld + SigningSpec) β)
    (hnext : ∀ answer, (next answer).IsQueryBoundP
      (IsSigningQuery (spec := OracleWorld) (Msg := Message) (Sig := Signature) (L := lifetime)) 0) :
    (liftM ((OracleWorld + SigningSpec).query (.inr request)) >>= next).IsQueryBoundP
      (IsSigningQuery (spec := OracleWorld) (Msg := Message) (Sig := Signature) (L := lifetime)) 1 := by
  rw [OracleComp.isQueryBoundP_query_bind_iff]
  exact ⟨Or.inr Nat.one_pos, fun answer => by simpa [IsSigningQuery] using hnext answer⟩

theorem chainMutation_oneRequest : OneRequest chainMutationSufCmaAdversary := fun _ =>
  oneRequest_of_request_then _ _ fun _ => by
    simpa using liftPrivateSamples_noRequest mutationChoice

theorem neighbor_oneRequest : OneRequest neighborSufCmaAdversary := fun publicKey =>
  oneRequest_of_request_then _ _ fun answer => by
    simpa using liftWorldToAdversary_noRequest (neighborAfterSigning publicKey answer)

theorem replay_oneRequest : OneRequest EUFCMA.replayStatementAdversary := fun publicKey =>
  oneRequest_of_request_then _ _ fun answer => by
    simpa using liftWorldToAdversary_noRequest (EUFCMA.replayAfterSigning publicKey answer)

theorem modeOf_hash_sign :
    Modes.modeOf {QueryKind.hash, QueryKind.sign} = ⟨false, false, false, true⟩ := by decide

theorem modeOf_hash : Modes.modeOf {QueryKind.hash} = CountingMode.direct := by decide

theorem modeOf_univ : Modes.modeOf Finset.univ = CountingMode.everything := by decide

/-! ### The attacks in the statement's games -/

theorem paper_chainMutation_requests_attack :
    ¬(SUFCMA.securityGame (PK := PublicKey) (SK := Seeded.SecretKey)).HasClassicalSecurityBits
      xmss {QueryKind.hash, QueryKind.sign} (122 + 1) := by
  intro h
  have hsecure := Modes.notion_oneRequest_bound _ (by decide) xmss _ h
  rw [modeOf_hash_sign] at hsecure
  have hbound := hsecure 1 le_rfl chainMutationSufCmaAdversary chainMutation_oneRequest
    chainMutation_requests_queryBound
  rw [chainMutation_requests_advantage, Nat.cast_one] at hbound
  exact (not_lt_of_ge hbound) chainMutation_seeded_advantage_exceeds_123

theorem paper_neighbor_everything_attack :
    ¬(SUFCMA.securityGame (PK := PublicKey) (SK := Seeded.SecretKey)).HasClassicalSecurityBits
      xmss Finset.univ (127 + 1) := by
  intro h
  have hsecure := Modes.notion_oneRequest_bound _ (by simp) xmss _ h
  rw [modeOf_univ] at hsecure
  have hbound := hsecure neighborEverythingBudget (by norm_num [neighborEverythingBudget])
    neighborSufCmaAdversary neighbor_oneRequest neighbor_everything_queryBound
  rw [neighbor_everything_advantage, neighborEverythingBudget_ratio] at hbound
  exact (not_lt_of_ge hbound) neighbor_seeded_advantage_exceeds_five_sixtyfourths

theorem paper_replay_direct_attack :
    ¬(EUFCMA.securityGame (PK := PublicKey) (SK := Seeded.SecretKey)).HasClassicalSecurityBits
      xmss {QueryKind.hash} (126 + 1) := by
  intro h
  have hsecure := Modes.eufNotion_oneRequest_bound _ (by decide) xmss _ h
  rw [modeOf_hash] at hsecure
  have hbound := hsecure 1 le_rfl EUFCMA.replayStatementAdversary replay_oneRequest
    EUFCMA.replay_statement_direct_queryBound
  rw [EUFCMA.notion_advantage_eq, Nat.cast_one, one_div] at hbound
  exact (not_lt_of_ge hbound) EUFCMA.replay_seeded_advantage_exceeds_127

theorem paper_neighbor_euf_everything_attack :
    ¬(EUFCMA.securityGame (PK := PublicKey) (SK := Seeded.SecretKey)).HasClassicalSecurityBits
      xmss Finset.univ 128 := by
  intro h
  have hsecure := Modes.eufNotion_oneRequest_bound _ (by simp) xmss _ h
  rw [modeOf_univ] at hsecure
  have hbound := hsecure neighborEverythingBudget (by norm_num [neighborEverythingBudget])
    neighborSufCmaAdversary neighbor_oneRequest neighbor_euf_everything_queryBound
  rw [neighbor_euf_everything_advantage, neighborEverythingBudget_ratio] at hbound
  exact (not_lt_of_ge hbound) neighbor_seeded_advantage_exceeds_five_sixtyfourths

end XmssSecurity.TargetSum.Attack

namespace XmssSecurity.TargetSum.Proof

open SUFCMA Attack

/-- The exact strong-unforgeability classification in the statement's game. -/
theorem sufCma_exact_of_hash_mem (Z : Finset QueryKind) (hZ : QueryKind.hash ∈ Z) :
    (SUFCMA.securityGame (PK := PublicKey) (SK := Seeded.SecretKey)).HasExactClassicalSecurityBits
      xmss Z
      (if QueryKind.keygen ∈ Z ∨ QueryKind.signer ∈ Z ∨ QueryKind.verifier ∈ Z then 127 else 122) := by
  refine ⟨SUFCMA.hasClassicalSecurityBits_of_lossy _ xmss Z _ (lossySufCma_exact_of_hash_mem Z hZ).1,
    fun hsecure => ?_⟩
  split_ifs at hsecure with h1
  · exact paper_neighbor_everything_attack
      (Modes.securityGame_hasClassicalSecurityBits_mono _ xmss (Finset.subset_univ Z) hsecure)
  · refine paper_chainMutation_requests_attack
      (Modes.securityGame_hasClassicalSecurityBits_mono _ xmss (fun kind hkind => ?_) hsecure)
    cases kind <;> simp_all

/-- The exact standard-unforgeability classification in the statement's game. -/
theorem eufCma_exact_of_hash_mem (Z : Finset QueryKind) (hZ : QueryKind.hash ∈ Z) :
    (EUFCMA.securityGame (PK := PublicKey) (SK := Seeded.SecretKey)).HasExactClassicalSecurityBits
      xmss Z
      (if QueryKind.keygen ∈ Z ∨ QueryKind.signer ∈ Z ∨ QueryKind.verifier ∈ Z ∨
        QueryKind.sign ∈ Z then 127 else 126) := by
  refine ⟨SUFCMA.hasClassicalSecurityBits_of_lossy _ xmss Z _ (lossyEufCma_exact_of_hash_mem Z hZ).1,
    fun hsecure => ?_⟩
  split_ifs at hsecure with h1
  · exact paper_neighbor_euf_everything_attack
      (Modes.securityGame_hasClassicalSecurityBits_mono _ xmss (Finset.subset_univ Z) hsecure)
  · refine paper_replay_direct_attack
      (Modes.securityGame_hasClassicalSecurityBits_mono _ xmss (fun kind hkind => ?_) hsecure)
    cases kind <;> simp_all

end XmssSecurity.TargetSum.Proof
