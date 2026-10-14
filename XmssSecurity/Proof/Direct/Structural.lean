import XmssSecurity.Proof.Direct.Basic
import XmssSecurity.Proof.CappedJointExactLoss

/-!
# The structural-collision term under a direct query bound

`expectedPostKeygenStructuralQueries` counts, after key generation, the expected number of hash
queries whose input is moved by `keygenStructuralTargetInput` (chain, leaf and Merkle inputs that
collide with key generation). The signer only queries encoding-domain inputs, which are never
moved, so only the adversary's own hash queries and those of the final verification count. This
bounds the term by `D + verifierQueryBound` when the adversary makes at most `D` direct hash
queries.
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity

namespace Direct

theorem tsum_probOutput_mul_le {β : Type} (computation : ProbComp β) (f : β → ℝ≥0∞) (bound : ℝ≥0∞)
    (h : ∀ x, f x ≤ bound) :
    ∑' x, Pr[= x | computation] * f x ≤ bound :=
  calc
    _ ≤ ∑' x, Pr[= x | computation] * bound :=
      ENNReal.tsum_le_tsum fun x => by gcongr; exact h x
    _ = (∑' x, Pr[= x | computation]) * bound := ENNReal.tsum_mul_right
    _ ≤ 1 * bound := by gcongr; exact tsum_probOutput_le_one
    _ = bound := one_mul _

/-! ## The signer makes no structural query -/

theorem precomputedSignAttempt_structural_zero (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (leafIndex : LeafIndex) (message : Message)
    (randomness : Randomness) :
    (Concrete.precomputedSignAttempt secretKey leafIndex message randomness :
      OracleComp HashSpec (Option Signature)).IsQueryBoundP
        (fun input => keygenStructuralTargetInput secretKey cache input ≠ input) 0 := by
  rw [Concrete.precomputedSignAttempt]
  refine OracleComp.isQueryBoundP_bind (n := 0) (m := 0) ?_ ?_
  · have hself := keygenStructuralTargetInput_encodingInput secretKey cache leafIndex
      (message, randomness)
    simp only [Concrete.CacheView.encodingInput] at hself
    simp [Concrete.encodingHash, Concrete.tweakableHash, Concrete.oracleHash, hself]
  · intro digest _
    split <;> simp

theorem liftM_precomputedSignAttempt_structural_zero (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (leafIndex : LeafIndex) (message : Message)
    (randomness : Randomness) :
    (liftM (Concrete.precomputedSignAttempt secretKey leafIndex message randomness :
      OracleComp HashSpec (Option Signature)) : OracleComp OracleWorld (Option Signature)).IsQueryBoundP
        (Rom.IsRelevantHashQuery fun input =>
          keygenStructuralTargetInput secretKey cache input ≠ input) 0 := by
  change (liftComp (Concrete.precomputedSignAttempt secretKey leafIndex message randomness :
    OracleComp HashSpec (Option Signature)) OracleWorld).IsQueryBoundP _ _
  exact OracleComp.IsQueryBoundP.liftComp_subSpec
    (p := fun input => keygenStructuralTargetInput secretKey cache input ≠ input)
    (fun _ => Iff.rfl)
    (precomputedSignAttempt_structural_zero secretKey cache leafIndex message randomness)

theorem liftM_probComp_structural_zero {β : Type} (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (computation : ProbComp β) :
    (liftM computation : OracleComp OracleWorld β).IsQueryBoundP
        (Rom.IsRelevantHashQuery fun input =>
          keygenStructuralTargetInput secretKey cache input ≠ input) 0 :=
  OracleComp.IsQueryBoundP.liftComp_subSpec
    (p := fun _ : unifSpec.Domain => False)
    (fun _ => Iff.rfl)
    (OracleComp.isQueryBoundP_false computation 0)

theorem precomputedSignBoundedAttempts_structural_zero (attempts : ℕ) (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (leafIndex : LeafIndex) (message : Message) :
    (Concrete.precomputedSignBoundedAttempts attempts secretKey leafIndex message).IsQueryBoundP
        (Rom.IsRelevantHashQuery fun input =>
          keygenStructuralTargetInput secretKey cache input ≠ input) 0 := by
  induction attempts with
  | zero =>
      rw [Concrete.precomputedSignBoundedAttempts]
      exact OracleComp.isQueryBoundP_pure _ _ _
  | succ attempts ih =>
      rw [Concrete.precomputedSignBoundedAttempts]
      refine OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
        (liftM_probComp_structural_zero secretKey cache _) ?_
      intro randomness _
      refine OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
        (liftM_precomputedSignAttempt_structural_zero secretKey cache leafIndex message
          randomness) ?_
      intro result _
      cases result with
      | none => exact ih
      | some signature => exact OracleComp.isQueryBoundP_pure _ _ _

theorem expectedStructuralQueries_sign_eq_zero (secretKey : SecretKey)
    (cache initialCache : QueryCache HashSpec) (leafIndex : LeafIndex) (message : Message) :
    expectedSimulatedQueryCount romImpl
        (Rom.IsRelevantHashQuery fun input =>
          keygenStructuralTargetInput secretKey cache input ≠ input)
        (Concrete.scheme.sign secretKey leafIndex message) initialCache = 0 := by
  have hbound : (Concrete.scheme.sign secretKey leafIndex message).IsQueryBoundP
      (Rom.IsRelevantHashQuery fun input =>
        keygenStructuralTargetInput secretKey cache input ≠ input) 0 := by
    change (Concrete.precomputedCappedSign secretKey leafIndex message).IsQueryBoundP _ 0
    rw [Concrete.precomputedCappedSign]
    exact precomputedSignBoundedAttempts_structural_zero _ secretKey cache leafIndex message
  have h := expectedSimulatedQueryCount_le_of_isQueryBoundP romImpl _ _ initialCache 0 hbound
  simpa using h

/-! ## The adversary part -/

/-- Under the source mapping of the adversary's actions, a predicate that no uniform query and no
signer run satisfies is counted at most once per direct hash query. -/
theorem expectedSimulatedQueryCount_mappedAdversary_le
    (publicKey : PublicKey) (secretKey : SecretKey)
    (P : OracleWorld.Domain → Prop) [DecidablePred P]
    (hunif : ∀ input, ¬P (.inl input))
    (hsign : ∀ (request : SignRequest) (cache : QueryCache HashSpec),
      expectedSimulatedQueryCount romImpl P
        (Concrete.scheme.sign secretKey request.epoch request.message) cache = 0)
    {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α) (n : ℕ)
    (hbound : computation.IsQueryBoundP IsDirectHashQuery n) (cache : QueryCache HashSpec) :
    expectedSimulatedQueryCount romImpl P
        (simulateQ (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey) computation)
        cache ≤ n := by
  induction computation using OracleComp.inductionOn generalizing n cache with
  | pure value => simp
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      rw [simulateQ_bind, simulateQ_query]
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map]
      rcases input with (worldInput | request)
      · change expectedSimulatedQueryCount romImpl P
          (liftM (OracleWorld.query worldInput) >>= fun answer =>
            simulateQ (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey)
              (next answer)) cache ≤ n
        rw [expectedSimulatedQueryCount_query_bind]
        rcases worldInput with uniformInput | hashInput
        · rw [if_neg (hunif uniformInput), zero_add]
          apply tsum_probOutput_mul_le
          intro result
          exact ih result.1 n (by simpa using hbound.2 result.1) result.2
        · have hpos : 0 < n := hbound.1.resolve_left (by simp)
          have hrest : ∑' result, Pr[= result | (romImpl (.inr hashInput)).run cache] *
              expectedSimulatedQueryCount romImpl P
                (simulateQ (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey)
                  (next result.1)) result.2 ≤ ((n - 1 : ℕ) : ℝ≥0∞) := by
            apply tsum_probOutput_mul_le
            intro result
            exact ih result.1 (n - 1) (by simpa using hbound.2 result.1) result.2
          calc
            _ ≤ 1 + ((n - 1 : ℕ) : ℝ≥0∞) := by
              gcongr
              split_ifs <;> simp
            _ = n := by
              rw [← Nat.cast_one, ← Nat.cast_add, Nat.add_sub_of_le hpos]
      · change expectedSimulatedQueryCount romImpl P
          (Concrete.scheme.sign secretKey request.epoch request.message >>= fun answer =>
            simulateQ (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey)
              (next answer)) cache ≤ n
        rw [expectedSimulatedQueryCount_bind, hsign, zero_add]
        apply tsum_probOutput_mul_le
        intro result
        exact ih result.1 n (by simpa using hbound.2 result.1) result.2

end Direct

/-! ## The bound -/

open Direct in

theorem expectedPostKeygenStructuralQueries_le_direct (adversary : Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D)
    (hverify : ∀ (publicKey : PublicKey) (leafIndex : LeafIndex) (message : Message)
      (signature : Signature) (cache : QueryCache HashSpec),
      HashQueryBound (Concrete.scheme.verify publicKey leafIndex message signature) cache
        Direct.verifierQueryBound) :
    expectedPostKeygenStructuralQueries adversary ≤ (D + Direct.verifierQueryBound : ℕ) := by
  unfold expectedPostKeygenStructuralQueries
  apply tsum_probOutput_mul_le
  intro keyResult
  unfold cappedSourceUnloggedDetailedGameAfterKeygen
  rw [expectedSimulatedQueryCount_bind]
  rw [Nat.cast_add]
  gcongr
  · exact expectedSimulatedQueryCount_mappedAdversary_le keyResult.1.1 keyResult.1.2 _
      (fun input => by simp [Rom.IsRelevantHashQuery])
      (fun request cache => expectedStructuralQueries_sign_eq_zero keyResult.1.2 keyResult.2
        cache request.epoch request.message)
      (adversary.main keyResult.1.1) D (hD keyResult.1.1) keyResult.2
  · apply tsum_probOutput_mul_le
    intro result
    rw [expectedSimulatedQueryCount_bind]
    simp only [expectedSimulatedQueryCount_pure, mul_zero, tsum_zero, add_zero]
    calc
      _ ≤ expectedSimulatedQueryCount romImpl IsHashQuery
          (Concrete.scheme.verify keyResult.1.1 result.1.epoch result.1.message
            result.1.signature) result.2 := by
        apply expectedSimulatedQueryCount_mono
        intro input hinput
        cases input with
        | inl index => simp [Rom.IsRelevantHashQuery] at hinput
        | inr hashInput => simp [IsHashQuery]
      _ ≤ _ := expectedSimulatedHashQueryCount_le _ _ _ (hverify _ _ _ _ _)

theorem winningStructuralCollision_probability_le_direct (adversary : Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D)
    (hverify : ∀ (publicKey : PublicKey) (leafIndex : LeafIndex) (message : Message)
      (signature : Signature) (cache : QueryCache HashSpec),
      HashQueryBound (Concrete.scheme.verify publicKey leafIndex message signature) cache
        Direct.verifierQueryBound) :
    Pr[fun execution : CappedEncodingTraceExecution =>
        WinningStructuralCollisionOccurs execution.2.1.1 execution.1 |
      cappedDetailedGameWithEncodingTrace adversary] ≤
      ((D + Direct.verifierQueryBound : ℕ) : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  calc
    _ = Pr[fun execution : GameOutcome × QueryCache HashSpec =>
          WinningStructuralCollisionOccurs execution.2 execution.1 |
        detailedGameWithCache Concrete.scheme adversary] := by
      rw [← cappedDetailedGameWithEncodingTrace_cache_projection, probEvent_map]
      rfl
    _ ≤ expectedPostKeygenStructuralQueries adversary / ((2 ^ digestBits : Nat) : ℝ≥0∞) :=
      winningStructuralCollision_probability_le_expectedPostKeygenStructuralQueries adversary
    _ ≤ _ := by
      gcongr
      exact expectedPostKeygenStructuralQueries_le_direct adversary D hD hverify

end XmssSecurity
