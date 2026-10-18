import XmssSecurity.Proof.TargetSum.EUFCMA.RequestsBasic
import XmssSecurity.Proof.TargetSum.Direct.SeedQueryPartition
import XmssSecurity.Proof.TargetSum.Direct.ReferenceSeedQueries
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Expected encoding, structural, seed, and signing-request counts share one
budget. Keeping these classes disjoint retains the credit of each signing call. -/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.TargetSum.EUFCMA.Requests
open XmssSecurity.EUFCMA

theorem memoize_isQueryBound {α : Type} (computation : OracleComp (OracleWorld + Generic.SigningSpec) α)
    (cache : QueryCache Generic.SigningSpec) (q : ℕ) (h : computation.IsQueryBoundP IsCharged q) :
    (Generic.DeterministicSigning.memoize computation cache).IsQueryBoundP IsCharged q := by
  induction computation using OracleComp.inductionOn generalizing cache q with
  | pure value => simp [Generic.DeterministicSigning.memoize_pure]
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at h
      cases input with
      | inl input =>
          rw [Generic.DeterministicSigning.memoize_base, isQueryBoundP_query_bind_iff]
          exact ⟨h.1, fun answer => ih answer cache _ (h.2 answer)⟩
      | inr request =>
          rw [Generic.DeterministicSigning.memoize_request]
          cases hc : cache request with
          | some answer =>
              exact (ih answer cache (q - 1) (by simpa using h.2 answer)).mono (Nat.sub_le q 1)
          | none =>
              rw [isQueryBoundP_query_bind_iff]
              exact ⟨h.1, fun answer => ih answer _ _ (h.2 answer)⟩

theorem IsQueryBound.memo {adversary : Generic.Adversary} {q : ℕ}
    (h : IsQueryBound adversary q) : IsQueryBound (Generic.Seeded.memoAdversary adversary) q :=
  fun publicKey => memoize_isQueryBound _ ∅ q (h publicKey)

def IsSigningRequest : (OracleWorld + Generic.SigningSpec).Domain → Prop
  | .inr _ => True
  | .inl _ => False

instance : DecidablePred IsSigningRequest := fun input =>
  match input with
  | .inr _ => inferInstanceAs (Decidable True)
  | .inl _ => inferInstanceAs (Decidable False)

theorem charged_iff (input : (OracleWorld + Generic.SigningSpec).Domain) :
    IsCharged input ↔ Generic.Direct.IsDirectHashQuery input ∨ IsSigningRequest input := by
  rcases input with (sample | hashInput) | request <;>
    simp [IsCharged, isCharged, Generic.Direct.IsDirectHashQuery, Generic.Direct.isDirectHashQuery, IsSigningRequest]

theorem direct_signing_disjoint (input : (OracleWorld + Generic.SigningSpec).Domain) :
    ¬(Generic.Direct.IsDirectHashQuery input ∧ IsSigningRequest input) := by
  rcases input with (sample | hashInput) | request <;>
    simp [Generic.Direct.IsDirectHashQuery, Generic.Direct.isDirectHashQuery, IsSigningRequest]

theorem expectedDirect_add_signing_le {α State : Type}
    (impl : QueryImpl (OracleWorld + Generic.SigningSpec) (StateT State ProbComp))
    (computation : OracleComp (OracleWorld + Generic.SigningSpec) α) (state : State) (q : ℕ)
    (hbound : computation.IsQueryBoundP IsCharged q) :
    expectedSimulatedQueryCount impl Generic.Direct.IsDirectHashQuery computation state +
      expectedSimulatedQueryCount impl IsSigningRequest computation state ≤ q := by
  rw [← expectedSimulatedQueryCount_or_of_disjoint impl _ _ direct_signing_disjoint]
  exact (expectedSimulatedQueryCount_mono impl _ IsCharged
    (fun input h => (charged_iff input).mpr h) computation state).trans
      (expectedSimulatedQueryCount_le_of_isQueryBoundP impl IsCharged computation state q hbound)

theorem expectedClasses_add_signing_le {α State : Type}
    (impl : QueryImpl (OracleWorld + Generic.SigningSpec) (StateT State ProbComp))
    (secretKey : Generic.SecretKey) (targetCache : QueryCache HashSpec)
    (computation : OracleComp (OracleWorld + Generic.SigningSpec) α) (state : State) (q : ℕ)
    (hbound : computation.IsQueryBoundP IsCharged q) :
    expectedSimulatedQueryCount impl (Generic.Direct.IsDirectEncodingQuery secretKey.parameter) computation state +
      expectedSimulatedQueryCount impl (Generic.Direct.IsDirectStructuralQuery secretKey targetCache) computation state +
      expectedSimulatedQueryCount impl Direct.IsDirectSeedQuery computation state +
      expectedSimulatedQueryCount impl IsSigningRequest computation state ≤ q :=
  (add_le_add (Direct.expectedDirect_classes_le impl secretKey targetCache computation state) le_rfl).trans
    (expectedDirect_add_signing_le impl computation state q hbound)

noncomputable def expectedSigningRequests (adversary : Generic.Adversary) : ℝ≥0∞ :=
  ∑' keyResult, Pr[= keyResult | (simulateQ Generic.romImpl Generic.Concrete.scheme.keygen).run ∅] *
    expectedSimulatedQueryCount (Generic.cappedUnloggedMappedAdversaryImpl keyResult.1.1 keyResult.1.2)
      IsSigningRequest (adversary.main keyResult.1.1) keyResult.2

theorem expected_class_budget (adversary : Generic.Adversary) (q : ℕ)
    (hbound : IsQueryBound adversary q) :
    Generic.Direct.expectedDirectEncodingQueries adversary + Generic.Direct.expectedDirectStructuralQueries adversary +
      Direct.expectedDirectSeedQueries adversary + expectedSigningRequests adversary ≤ q := by
  unfold Generic.Direct.expectedDirectEncodingQueries Generic.Direct.expectedDirectStructuralQueries
    Direct.expectedDirectSeedQueries expectedSigningRequests
  rw [← ENNReal.tsum_add, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
  simp_rw [← mul_add]
  apply Generic.Direct.tsum_probOutput_mul_le
  intro keyResult
  exact expectedClasses_add_signing_le _ _ _ _ _ q (hbound _)

/-- info: 'XmssSecurity.TargetSum.EUFCMA.Requests.expected_class_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms expected_class_budget

end XmssSecurity.TargetSum.EUFCMA.Requests
