import Xmss.Proof.Checksum.Main.Unforgeability
import Xmss.Proof.Common.RepeatedEpochs
import Xmss.Proof.Checksum.Code
import Xmss.Proof.Checksum.EncodingProbability

/-!
# The classifications in the statement's games

The classifications of `Main/StrongUnforgeability.lean` and `Main/Unforgeability.lean` are for the
lossy games, in which a repeated epoch loses. This file transfers them to the statement's games,
in which a repeated epoch is answered by `⊥` (`Proof/Common/RepeatedEpochs.lean`): the security
bounds transfer for every adversary, and every attack makes a single signing request, so it has
the same experiment in both games.
-/

open OracleComp OracleSpec ENNReal

namespace Xmss.Checksum.Attack

open Unforgeability SUFCMA

theorem liftPrivateSamples_noRequest {α : Type} (computation : ProbComp α) :
    (Generic.Attack.liftPrivateSamples computation).IsQueryBoundP
      (IsSigningQuery (spec := OracleWorld) (Msg := Message) (Sig := Generic.Signature) (L := lifetime)) 0 := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [Generic.Attack.liftPrivateSamples]
  | query_bind input next ih =>
      simp only [Generic.Attack.liftPrivateSamples, simulateQ_bind, simulateQ_spec_query] at ih ⊢
      refine (OracleComp.isQueryBoundP_query_bind_iff _ _ _ _).2
        ⟨Or.inl (by simp [IsSigningQuery]), fun answer => ?_⟩
      simpa [IsSigningQuery] using ih answer

theorem liftWorldToAdversary_noRequest {α : Type} (computation : OracleComp OracleWorld α) :
    (liftWorldToAdversary computation).IsQueryBoundP
      (IsSigningQuery (spec := OracleWorld) (Msg := Message) (Sig := Generic.Signature) (L := lifetime)) 0 :=
  liftWorldToAdversary_queryBound computation (fun _ => False) _ (fun _ => by simp [IsSigningQuery])
    0 (by induction computation using OracleComp.inductionOn <;> simp_all)

theorem oneRequest_of_request_then {β : Type} (request : Generic.SignRequest)
    (next : Option Generic.Signature → OracleComp (OracleWorld + Generic.SigningSpec) β)
    (hnext : ∀ answer, (next answer).IsQueryBoundP
      (IsSigningQuery (spec := OracleWorld) (Msg := Message) (Sig := Generic.Signature) (L := lifetime)) 0) :
    (liftM ((OracleWorld + Generic.SigningSpec).query (.inr request)) >>= next).IsQueryBoundP
      (IsSigningQuery (spec := OracleWorld) (Msg := Message) (Sig := Generic.Signature) (L := lifetime)) 1 := by
  rw [OracleComp.isQueryBoundP_query_bind_iff]
  exact ⟨Or.inr Nat.one_pos, fun answer => by simpa [IsSigningQuery] using hnext answer⟩

theorem oneRequestMain_oneRequest (finish : Option Generic.Signature → ChainIndex × Digest → Generic.Forgery)
    (choices : ProbComp (ChainIndex × Digest)) :
    (oneRequestMain finish choices).IsQueryBoundP
      (IsSigningQuery (spec := OracleWorld) (Msg := Message) (Sig := Generic.Signature) (L := lifetime)) 1 :=
  oneRequest_of_request_then _ _ fun _ => by
    simpa using liftPrivateSamples_noRequest choices

theorem chainMutation_oneRequest : OneRequest Generic.Attack.chainMutationSufCmaAdversary := fun _ =>
  oneRequest_of_request_then _ _ fun _ => by
    simpa using liftPrivateSamples_noRequest Generic.Attack.mutationChoice

theorem neighbor_oneRequest : OneRequest neighborSufCmaAdversary := fun publicKey =>
  oneRequest_of_request_then _ _ fun answer => by
    simpa using liftWorldToAdversary_noRequest (neighborAfterSigning publicKey answer)

theorem fresh_oneRequest : OneRequest freshSufCmaAdversary := fun _ =>
  oneRequestMain_oneRequest _ _

theorem modeOf_hash_sign :
    Modes.modeOf {QueryKind.hash, QueryKind.sign} = ⟨false, false, false, true⟩ := by decide

theorem modeOf_hash_signer :
    Modes.modeOf {QueryKind.hash, QueryKind.signer} = ⟨false, true, false, false⟩ := by decide

theorem modeOf_hash_signer_sign :
    Modes.modeOf {QueryKind.hash, QueryKind.signer, QueryKind.sign} = ⟨false, true, false, true⟩ := by
  decide

theorem modeOf_univ : Modes.modeOf Finset.univ = CountingMode.everything := by decide

/-! ### The attacks in the statement's games -/

theorem paper_chainMutation_requests_attack :
    ¬(SUFCMA.securityGame (PK := PublicKey) (SK := Generic.Seeded.SecretKey)).HasClassicalSecurityBits
      Generic.xmss {QueryKind.hash, QueryKind.sign} (122 + 1) := by
  intro h
  have hsecure := Modes.notion_oneRequest_bound _ (by decide) Generic.xmss _ h
  rw [modeOf_hash_sign] at hsecure
  have hbound := hsecure 1 le_rfl Generic.Attack.chainMutationSufCmaAdversary chainMutation_oneRequest
    Generic.Attack.chainMutation_requests_queryBound
  rw [Generic.Attack.chainMutation_requests_advantage, Nat.cast_one] at hbound
  exact (not_lt_of_ge hbound) chainMutation_seeded_advantage_exceeds_123

theorem paper_chainMutation_signer_attack :
    ¬(SUFCMA.securityGame (PK := PublicKey) (SK := Generic.Seeded.SecretKey)).HasClassicalSecurityBits
      Generic.xmss {QueryKind.hash, QueryKind.signer} (123 + 1) := by
  intro h
  have hsecure := Modes.notion_oneRequest_bound _ (by decide) Generic.xmss _ h
  rw [modeOf_hash_signer] at hsecure
  have hbound := hsecure 2 (by norm_num) Generic.Attack.chainMutationSufCmaAdversary chainMutation_oneRequest
    (by simpa using chainMutation_signer_queryBound false)
  rw [chainMutation_signer_advantage] at hbound
  apply (not_lt_of_ge hbound)
  refine lt_of_eq_of_lt ?_ chainMutation_seeded_advantage_exceeds_123
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_div]

theorem paper_chainMutation_signerRequests_attack :
    ¬(SUFCMA.securityGame (PK := PublicKey) (SK := Generic.Seeded.SecretKey)).HasClassicalSecurityBits
      Generic.xmss {QueryKind.hash, QueryKind.signer, QueryKind.sign} (124 + 1) := by
  intro h
  have hsecure := Modes.notion_oneRequest_bound _ (by decide) Generic.xmss _ h
  rw [modeOf_hash_signer_sign] at hsecure
  have hbound := hsecure 3 (by norm_num) Generic.Attack.chainMutationSufCmaAdversary chainMutation_oneRequest
    (by simpa using chainMutation_signer_queryBound true)
  rw [chainMutation_signer_advantage] at hbound
  apply (not_lt_of_ge hbound)
  refine lt_of_le_of_lt ?_ chainMutation_seeded_advantage_exceeds_123
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_div]

theorem paper_neighbor_everything_attack :
    ¬(SUFCMA.securityGame (PK := PublicKey) (SK := Generic.Seeded.SecretKey)).HasClassicalSecurityBits
      Generic.xmss Finset.univ (127 + 1) := by
  intro h
  have hsecure := Modes.notion_oneRequest_bound _ (by simp) Generic.xmss _ h
  rw [modeOf_univ] at hsecure
  have hbound := hsecure neighborEverythingBudget (by norm_num [neighborEverythingBudget])
    neighborSufCmaAdversary neighbor_oneRequest neighbor_everything_queryBound
  rw [neighbor_everything_advantage, neighborEverythingBudget_ratio] at hbound
  exact (not_lt_of_ge hbound) neighbor_seeded_advantage_exceeds_nine_thirtyseconds

theorem paper_freshMessage_attack (signer requests : Bool) (bits : ℕ) (Z : Finset QueryKind)
    (hZ : QueryKind.hash ∈ Z) (hmode : Modes.modeOf Z = ⟨false, signer, false, requests⟩)
    (hratio : (((if requests then 1 else 0) + (if signer then 2 else 0) : ℕ) : ℝ≥0∞) /
      ((2 ^ bits : ℕ) : ℝ≥0∞) ≤ 1 / ((2 ^ 123 : ℕ) : ℝ≥0∞))
    (hpositive : 1 ≤ (if requests then 1 else 0) + (if signer then 2 else 0)) :
    ¬(EUFCMA.securityGame (PK := PublicKey) (SK := Generic.Seeded.SecretKey)).HasClassicalSecurityBits
      Generic.xmss Z bits := by
  intro h
  have hsecure := Modes.eufNotion_oneRequest_bound _ hZ Generic.xmss _ h
  rw [hmode] at hsecure
  have hbound := hsecure _ hpositive freshSufCmaAdversary fresh_oneRequest
    (freshMessage_queryBound signer requests)
  exact (not_lt_of_ge ((freshMessage_standard_advantage_lower _).trans (hbound.trans hratio)))
    fresh_seeded_advantage_exceeds_123

theorem paper_neighbor_euf_everything_attack :
    ¬(EUFCMA.securityGame (PK := PublicKey) (SK := Generic.Seeded.SecretKey)).HasClassicalSecurityBits
      Generic.xmss Finset.univ 128 := by
  intro h
  have hsecure := Modes.eufNotion_oneRequest_bound _ (by simp) Generic.xmss _ h
  rw [modeOf_univ] at hsecure
  have hbound := hsecure neighborEverythingBudget (by norm_num [neighborEverythingBudget])
    neighborSufCmaAdversary neighbor_oneRequest neighbor_euf_everything_queryBound
  rw [neighbor_euf_everything_advantage, neighborEverythingBudget_ratio] at hbound
  exact (not_lt_of_ge hbound) neighbor_seeded_advantage_exceeds_nine_thirtyseconds

end Xmss.Checksum.Attack

namespace Xmss.Checksum

open Unforgeability SUFCMA Attack

/-- The exact strong-unforgeability classification in the statement's game. -/
theorem sufCma_exact_of_hash_mem (Z : Finset QueryKind) (hZ : QueryKind.hash ∈ Z) :
    (SUFCMA.securityGame (PK := PublicKey) (SK := Generic.Seeded.SecretKey)).HasExactClassicalSecurityBits
      Generic.xmss Z
      (if QueryKind.keygen ∈ Z ∨ QueryKind.verifier ∈ Z then 127
      else if QueryKind.signer ∈ Z then (if QueryKind.sign ∈ Z then 124 else 123)
      else 122) := by
  refine ⟨Unforgeability.hasClassicalSecurityBits_of_lossy _ Generic.xmss Z _ (lossySufCma_exact_of_hash_mem Z hZ).1,
    fun hsecure => ?_⟩
  split_ifs at hsecure with h1 h2 h3
  · exact paper_neighbor_everything_attack
      (Modes.securityGame_hasClassicalSecurityBits_mono _ Generic.xmss (Finset.subset_univ Z) hsecure)
  · refine paper_chainMutation_signerRequests_attack
      (Modes.securityGame_hasClassicalSecurityBits_mono _ Generic.xmss (fun kind hkind => ?_) hsecure)
    cases kind <;> simp_all
  · refine paper_chainMutation_signer_attack
      (Modes.securityGame_hasClassicalSecurityBits_mono _ Generic.xmss (fun kind hkind => ?_) hsecure)
    cases kind <;> simp_all
  · refine paper_chainMutation_requests_attack
      (Modes.securityGame_hasClassicalSecurityBits_mono _ Generic.xmss (fun kind hkind => ?_) hsecure)
    cases kind <;> simp_all

/-- The exact standard-unforgeability classification in the statement's game. -/
theorem eufCma_exact_of_hash_mem (Z : Finset QueryKind) (hZ : QueryKind.hash ∈ Z) :
    (EUFCMA.securityGame (PK := PublicKey) (SK := Generic.Seeded.SecretKey)).HasExactClassicalSecurityBits
      Generic.xmss Z
      (if QueryKind.keygen ∈ Z ∨ QueryKind.verifier ∈ Z then 127
      else if QueryKind.signer ∈ Z then (if QueryKind.sign ∈ Z then 124 else 123)
      else 122) := by
  refine ⟨Unforgeability.hasClassicalSecurityBits_of_lossy _ Generic.xmss Z _ (lossyEufCma_exact_of_hash_mem Z hZ).1,
    fun hsecure => ?_⟩
  split_ifs at hsecure with h1 h2 h3
  · exact paper_neighbor_euf_everything_attack
      (Modes.securityGame_hasClassicalSecurityBits_mono _ Generic.xmss (Finset.subset_univ Z) hsecure)
  · refine paper_freshMessage_attack true true 125 {QueryKind.hash, QueryKind.signer, QueryKind.sign}
      (by decide) modeOf_hash_signer_sign ?_ (by norm_num)
      (Modes.securityGame_hasClassicalSecurityBits_mono _ Generic.xmss (fun kind hkind => ?_) hsecure)
    · apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_div]
    · cases kind <;> simp_all
  · refine paper_freshMessage_attack true false 124 {QueryKind.hash, QueryKind.signer}
      (by decide) modeOf_hash_signer ?_ (by norm_num)
      (Modes.securityGame_hasClassicalSecurityBits_mono _ Generic.xmss (fun kind hkind => ?_) hsecure)
    · apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_div]
    · cases kind <;> simp_all
  · refine paper_freshMessage_attack false true 123 {QueryKind.hash, QueryKind.sign}
      (by decide) modeOf_hash_sign (by norm_num) (by norm_num)
      (Modes.securityGame_hasClassicalSecurityBits_mono _ Generic.xmss (fun kind hkind => ?_) hsecure)
    cases kind <;> simp_all

end Xmss.Checksum
