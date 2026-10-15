import XmssSecurity.Proof.EUFCMA.RequestsBasic
import XmssSecurity.Proof.Direct.SeedQueryPartition
import XmssSecurity.Proof.Direct.ReferenceSeedQueries

/-! Expected encoding, structural, seed, and signing-request counts share one
budget. Keeping these classes disjoint retains the credit of each signing call. -/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.EUFCMA.Requests

theorem memoize_isQueryBound {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache SigningSpec) (q : ℕ) (h : computation.IsQueryBoundP IsCharged q) :
    (DeterministicSigning.memoize computation cache).IsQueryBoundP IsCharged q := by
  induction computation using OracleComp.inductionOn generalizing cache q with
  | pure value => simp [DeterministicSigning.memoize_pure]
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at h
      cases input with
      | inl input =>
          rw [DeterministicSigning.memoize_base, isQueryBoundP_query_bind_iff]
          exact ⟨h.1, fun answer => ih answer cache _ (h.2 answer)⟩
      | inr request =>
          rw [DeterministicSigning.memoize_request]
          cases hc : cache request with
          | some answer =>
              exact (ih answer cache (q - 1) (by simpa using h.2 answer)).mono (Nat.sub_le q 1)
          | none =>
              rw [isQueryBoundP_query_bind_iff]
              exact ⟨h.1, fun answer => ih answer _ _ (h.2 answer)⟩

theorem IsQueryBound.memo {adversary : XmssSecurity.Adversary} {q : ℕ}
    (h : IsQueryBound adversary q) : IsQueryBound (XmssSecurity.Seeded.memoAdversary adversary) q :=
  fun publicKey => memoize_isQueryBound _ ∅ q (h publicKey)

def IsSigningRequest : (OracleWorld + SigningSpec).Domain → Prop
  | .inr _ => True
  | .inl _ => False

instance : DecidablePred IsSigningRequest := fun input =>
  match input with
  | .inr _ => inferInstanceAs (Decidable True)
  | .inl _ => inferInstanceAs (Decidable False)

theorem charged_iff (input : (OracleWorld + SigningSpec).Domain) :
    IsCharged input ↔ Direct.IsDirectHashQuery input ∨ IsSigningRequest input := by
  rcases input with (sample | hashInput) | request <;>
    simp [IsCharged, isCharged, Direct.IsDirectHashQuery, Direct.isDirectHashQuery, IsSigningRequest]

theorem direct_signing_disjoint (input : (OracleWorld + SigningSpec).Domain) :
    ¬(Direct.IsDirectHashQuery input ∧ IsSigningRequest input) := by
  rcases input with (sample | hashInput) | request <;>
    simp [Direct.IsDirectHashQuery, Direct.isDirectHashQuery, IsSigningRequest]

theorem expectedDirect_add_signing_le {α State : Type}
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT State ProbComp))
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : State) (q : ℕ)
    (hbound : computation.IsQueryBoundP IsCharged q) :
    expectedSimulatedQueryCount impl Direct.IsDirectHashQuery computation state +
      expectedSimulatedQueryCount impl IsSigningRequest computation state ≤ q := by
  rw [← expectedSimulatedQueryCount_or_of_disjoint impl _ _ direct_signing_disjoint]
  exact (expectedSimulatedQueryCount_mono impl _ IsCharged
    (fun input h => (charged_iff input).mpr h) computation state).trans
      (expectedSimulatedQueryCount_le_of_isQueryBoundP impl IsCharged computation state q hbound)

theorem expectedClasses_add_signing_le {α State : Type}
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT State ProbComp))
    (secretKey : SecretKey) (targetCache : QueryCache HashSpec)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : State) (q : ℕ)
    (hbound : computation.IsQueryBoundP IsCharged q) :
    expectedSimulatedQueryCount impl (Direct.IsDirectEncodingQuery secretKey.parameter) computation state +
      expectedSimulatedQueryCount impl (Direct.IsDirectStructuralQuery secretKey targetCache) computation state +
      expectedSimulatedQueryCount impl Direct.IsDirectSeedQuery computation state +
      expectedSimulatedQueryCount impl IsSigningRequest computation state ≤ q :=
  (add_le_add (Direct.expectedDirect_classes_le impl secretKey targetCache computation state) le_rfl).trans
    (expectedDirect_add_signing_le impl computation state q hbound)

noncomputable def expectedSigningRequests (adversary : XmssSecurity.Adversary) : ℝ≥0∞ :=
  ∑' keyResult, Pr[= keyResult | (simulateQ romImpl Concrete.scheme.keygen).run ∅] *
    expectedSimulatedQueryCount (cappedUnloggedMappedAdversaryImpl keyResult.1.1 keyResult.1.2)
      IsSigningRequest (adversary.main keyResult.1.1) keyResult.2

theorem expected_class_budget (adversary : XmssSecurity.Adversary) (q : ℕ)
    (hbound : IsQueryBound adversary q) :
    Direct.expectedDirectEncodingQueries adversary + Direct.expectedDirectStructuralQueries adversary +
      Direct.expectedDirectSeedQueries adversary + expectedSigningRequests adversary ≤ q := by
  unfold Direct.expectedDirectEncodingQueries Direct.expectedDirectStructuralQueries
    Direct.expectedDirectSeedQueries expectedSigningRequests
  rw [← ENNReal.tsum_add, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
  simp_rw [← mul_add]
  apply Direct.tsum_probOutput_mul_le
  intro keyResult
  exact expectedClasses_add_signing_le _ _ _ _ _ q (hbound _)

/-- info: 'XmssSecurity.EUFCMA.Requests.expected_class_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms expected_class_budget

end XmssSecurity.EUFCMA.Requests
