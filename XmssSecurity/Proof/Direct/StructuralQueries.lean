import XmssSecurity.Proof.Direct.EncodingPrehitExpected
import XmssSecurity.Proof.Direct.DecidingSecondLane

/-! Disjoint expected budgets for direct encoding and structural queries. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.Direct

def IsDirectWorldQuery (predicate : OracleWorld.Domain → Prop) :
    (OracleWorld + SigningSpec).Domain → Prop
  | .inl input => predicate input
  | .inr _ => False

noncomputable instance (predicate : OracleWorld.Domain → Prop) :
    DecidablePred (IsDirectWorldQuery predicate) := Classical.decPred _

theorem expectedSimulatedQueryCount_mappedAdversary_eq
    (publicKey : PublicKey) (secretKey : SecretKey)
    (predicate : OracleWorld.Domain → Prop) [DecidablePred predicate]
    (hsign : ∀ (request : SignRequest) (cache : QueryCache HashSpec),
      expectedSimulatedQueryCount romImpl predicate
        (Concrete.scheme.sign secretKey request.epoch request.message) cache = 0)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec) :
    expectedSimulatedQueryCount romImpl predicate
        (simulateQ (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey) computation) cache =
      expectedSimulatedQueryCount (cappedUnloggedMappedAdversaryImpl publicKey secretKey)
        (IsDirectWorldQuery predicate) computation cache := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_query]
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map]
      cases input with
      | inl worldInput =>
          change expectedSimulatedQueryCount romImpl predicate
              (liftM (OracleWorld.query worldInput) >>= fun answer =>
                simulateQ (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey)
                  (next answer)) cache = _
          rw [expectedSimulatedQueryCount_query_bind, expectedSimulatedQueryCount_query_bind]
          simp_rw [ih]
          by_cases h : predicate worldInput <;>
            simp only [IsDirectWorldQuery, h, if_true, if_false] <;> rfl
      | inr request =>
          change expectedSimulatedQueryCount romImpl predicate
              (Concrete.scheme.sign secretKey request.epoch request.message >>= fun answer =>
                simulateQ (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey)
                  (next answer)) cache = _
          rw [expectedSimulatedQueryCount_bind, hsign, zero_add,
            expectedSimulatedQueryCount_query_bind]
          simp only [IsDirectWorldQuery, if_false, zero_add]
          simp_rw [ih]
          rfl

def IsDirectStructuralQuery (secretKey : SecretKey) (cache : QueryCache HashSpec) :
    (OracleWorld + SigningSpec).Domain → Prop :=
  IsDirectWorldQuery (Rom.IsRelevantHashQuery fun input =>
    keygenStructuralTargetInput secretKey cache input ≠ input)

noncomputable instance (secretKey : SecretKey) (cache : QueryCache HashSpec) :
    DecidablePred (IsDirectStructuralQuery secretKey cache) := Classical.decPred _

theorem directEncoding_structural_disjoint
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (input : (OracleWorld + SigningSpec).Domain) :
    ¬(IsDirectEncodingQuery secretKey.parameter input ∧ IsDirectStructuralQuery secretKey cache input) := by
  rcases input with (uniform | hash) | request
  · rintro ⟨h, _⟩
    exact h.elim
  · rintro ⟨hencoding, hstructural⟩
    exact hstructural (encodingQuery_structuralTarget_fixed secretKey cache hash hencoding)
  · rintro ⟨h, _⟩
    exact h.elim

theorem directEncoding_or_structural_isDirectHashQuery
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (input : (OracleWorld + SigningSpec).Domain)
    (h : IsDirectEncodingQuery secretKey.parameter input ∨ IsDirectStructuralQuery secretKey cache input) :
    IsDirectHashQuery input := by
  rcases input with (uniform | hash) | request
  · rcases h with h | h <;> exact h.elim
  · exact isDirectHashQuery_hash hash
  · rcases h with h | h <;> exact h.elim

theorem expectedDirectEncoding_add_structural_le
    (publicKey : PublicKey) (secretKey : SecretKey)
    (targetCache initialCache : QueryCache HashSpec)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (D : ℕ) (hD : computation.IsQueryBoundP IsDirectHashQuery D) :
    expectedSimulatedQueryCount (cappedUnloggedMappedAdversaryImpl publicKey secretKey)
        (IsDirectEncodingQuery secretKey.parameter) computation initialCache +
      expectedSimulatedQueryCount (cappedUnloggedMappedAdversaryImpl publicKey secretKey)
        (IsDirectStructuralQuery secretKey targetCache) computation initialCache ≤ D := by
  rw [← expectedSimulatedQueryCount_or_of_disjoint _ _ _
    (directEncoding_structural_disjoint secretKey targetCache)]
  exact (expectedSimulatedQueryCount_mono _ _ _
    (directEncoding_or_structural_isDirectHashQuery secretKey targetCache) computation initialCache).trans
      (expectedSimulatedQueryCount_le_of_isQueryBoundP _ _ computation initialCache D hD)

theorem expectedStructuralQueries_adversaryPhase_eq (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : SecretKey) (targetCache initialCache : QueryCache HashSpec) :
    expectedSimulatedQueryCount romImpl
        (Rom.IsRelevantHashQuery fun input =>
          keygenStructuralTargetInput secretKey targetCache input ≠ input)
        (Deciding.adversaryPhase adversary publicKey secretKey) initialCache =
      expectedSimulatedQueryCount (cappedUnloggedMappedAdversaryImpl publicKey secretKey)
        (IsDirectStructuralQuery secretKey targetCache) (adversary.main publicKey) initialCache := by
  have hproj := QueryImpl.fst_map_run_withTraceAppend
    (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey) signingLogFragment
    (adversary.main publicKey)
  rw [cappedSourceUnloggedMappedAdversaryImpl_withTraceAppend_eq] at hproj
  have hcount := congrArg
    (fun computation => expectedSimulatedQueryCount romImpl
      (Rom.IsRelevantHashQuery fun input =>
        keygenStructuralTargetInput secretKey targetCache input ≠ input)
      computation initialCache) hproj
  rw [expectedSimulatedQueryCount_map] at hcount
  unfold Deciding.adversaryPhase
  rw [hcount]
  exact expectedSimulatedQueryCount_mappedAdversary_eq publicKey secretKey _
    (fun request cache => expectedStructuralQueries_sign_eq_zero secretKey targetCache cache
      request.epoch request.message) (adversary.main publicKey) initialCache

noncomputable def expectedDirectStructuralQueries (adversary : Adversary) : ℝ≥0∞ :=
  ∑' keyResult, Pr[= keyResult | (simulateQ romImpl Concrete.scheme.keygen).run ∅] *
    expectedSimulatedQueryCount
      (cappedUnloggedMappedAdversaryImpl keyResult.1.1 keyResult.1.2)
      (IsDirectStructuralQuery keyResult.1.2 keyResult.2)
      (adversary.main keyResult.1.1) keyResult.2

theorem expectedDirectEncodingQueries_add_structural_le (adversary : Adversary)
    (D : ℕ) (hD : IsDirectQueryBound adversary D) :
    expectedDirectEncodingQueries adversary + expectedDirectStructuralQueries adversary ≤ D := by
  unfold expectedDirectEncodingQueries expectedDirectStructuralQueries
  rw [← ENNReal.tsum_add]
  simp_rw [← mul_add]
  apply tsum_probOutput_mul_le
  intro keyResult
  exact expectedDirectEncoding_add_structural_le _ _ _ _ _ D (hD _)

end XmssSecurity.Direct
