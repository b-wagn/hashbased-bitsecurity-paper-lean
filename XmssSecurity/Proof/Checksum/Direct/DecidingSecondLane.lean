import XmssSecurity.Proof.Checksum.Direct.DecidingCollision
import XmssSecurity.Proof.Checksum.Direct.DecidingVerifierCount
import XmssSecurity.Proof.Checksum.Direct.ForgedEncodingQuery
import XmssSecurity.Proof.Checksum.Direct.Structural
import XmssSecurity.Proof.Checksum.GlobalBadEvent
import XmssSecurity.Proof.Checksum.CappedSuffixEventProbability
import XmssSecurity.Proof.Checksum.CappedMerkleEventProbability
import XmssSecurity.Proof.Checksum.ExpectedAdaptiveFreshTarget

/-!
# The second lane of the 122-bit direct-mode proof

The detailed game after key generation splits into the *adversary phase* (the adversary with its
oracles, cache `C_k → C_v`) and the *verification phase* (the verifier, cache `C_v → C_f`). For a
winning run without encoding event and without a revealed deciding chain value, either the
adversary phase exhibits a fresh structural collision with the key-generation cache (charged to the
adversary's `D` direct hash queries) or the verification phase exhibits a fresh collision on the
deciding path (charged to the verifier's at most `40` moved queries).

`decidingSecondLane_probability_le` assembles the bound `(D + 40) / 2^128` from the orientation,
cached-encoding, and verifier-count hypotheses. `decidingSecondLane_probability_le_direct`
discharges these hypotheses, including the extra query used to cache the forged encoding.
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.Checksum.Deciding

open Concrete

/-! ## Expected moved queries of the two phases -/

/-- The adversary phase makes, in expectation, at most `D` queries moved by the structural map:
only the adversary's own direct hash queries can be moved, the signer never queries a structural
input. -/
theorem expectedStructuralQueries_adversaryPhase_le (adversary : Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D) (publicKey : PublicKey)
    (secretKey : SecretKey) (cache initialCache : QueryCache HashSpec) :
    expectedSimulatedQueryCount romImpl
        (Rom.IsRelevantHashQuery fun input =>
          keygenStructuralTargetInput secretKey cache input ≠ input)
        (adversaryPhase adversary publicKey secretKey) initialCache ≤ D := by
  have hproj := QueryImpl.fst_map_run_withTraceAppend
    (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey) signingLogFragment
    (adversary.main publicKey)
  rw [cappedSourceUnloggedMappedAdversaryImpl_withTraceAppend_eq] at hproj
  have hcount := congrArg
    (fun computation => expectedSimulatedQueryCount romImpl
      (Rom.IsRelevantHashQuery fun input =>
        keygenStructuralTargetInput secretKey cache input ≠ input)
      computation initialCache) hproj
  rw [expectedSimulatedQueryCount_map] at hcount
  unfold adversaryPhase
  rw [hcount]
  exact Direct.expectedSimulatedQueryCount_mappedAdversary_le publicKey secretKey _
    (fun input => by simp [Rom.IsRelevantHashQuery])
    (fun request cache' => Direct.expectedStructuralQueries_sign_eq_zero secretKey cache cache'
      request.epoch request.message)
    (adversary.main publicKey) D (hD publicKey) initialCache

/-- The verification phase has the verifier's expected query count. -/
theorem expectedQueries_verificationPhase_eq (P : OracleWorld.Domain → Prop) [DecidablePred P]
    (publicKey : PublicKey) (secretKey : SecretKey)
    (prefixResult : Forgery × QueryLog SigningSpec) (cache : QueryCache HashSpec) :
    expectedSimulatedQueryCount romImpl P (verificationPhase publicKey secretKey prefixResult)
        cache =
      expectedSimulatedQueryCount romImpl P
        (Concrete.scheme.verify publicKey prefixResult.1.epoch prefixResult.1.message
          prefixResult.1.signature) cache := by
  unfold verificationPhase
  rw [expectedSimulatedQueryCount_bind]
  simp only [expectedSimulatedQueryCount_pure, mul_zero, tsum_zero, add_zero]

/-! ## Key-generation facts -/

/-- The public and secret keys of a key-generation result share their parameter. -/
theorem keygen_publicKey_parameter_eq
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅)) :
    keyResult.1.1.parameter = keyResult.1.2.parameter := by
  have hkeygen' : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅) := by
    simpa only [Concrete.scheme] using hkeygen
  obtain ⟨parameter, secret, root, hkey, _⟩ := Concrete.keygen_support_rootTree _
    (Concrete.precomputedKeygen_support_oldKeygen keyResult hkeygen')
  have hpublic := congrArg (fun result : PublicKey × SecretKey => result.1.parameter) hkey
  have hsecret := congrArg (fun result : PublicKey × SecretKey => result.2.parameter) hkey
  exact hpublic.trans hsecret.symm

/-! ## Summation helpers -/

theorem tsum_probOutput_mul_le_of_mem_support {β : Type} (computation : ProbComp β)
    (f : β → ℝ≥0∞) (bound : ℝ≥0∞) (h : ∀ x ∈ support computation, f x ≤ bound) :
    ∑' x, Pr[= x | computation] * f x ≤ bound :=
  calc
    _ ≤ ∑' x, Pr[= x | computation] * bound := by
      apply ENNReal.tsum_le_tsum
      intro x
      by_cases hx : x ∈ support computation
      · gcongr
        exact h x hx
      · rw [probOutput_eq_zero_of_not_mem_support hx, zero_mul, zero_mul]
    _ ≤ bound := Direct.tsum_probOutput_mul_le _ _ _ fun _ => le_rfl

/-! ## The bound after key generation -/

/-- The second-lane event after key generation, for one key-generation result: either the
adversary phase produces a structural collision with the key-generation cache, or the verification
phase produces a collision on the deciding path. -/
theorem decidingSecondLane_afterKeygen_le (adversary : Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hcached : ∀ prefixResult ∈ support
        ((simulateQ romImpl (adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2),
        prefixResult.2 (Concrete.CacheView.encodingInput keyResult.1.2.parameter
          prefixResult.1.1.epoch
          (prefixResult.1.1.message, prefixResult.1.1.signature.randomness)) ≠ none)
    (horient : ∀ prefixResult ∈ support
        ((simulateQ romImpl (adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2),
        prefixResult.2 (Concrete.CacheView.encodingInput keyResult.1.2.parameter
          prefixResult.1.1.epoch
          (prefixResult.1.1.message, prefixResult.1.1.signature.randomness)) ≠ none →
        ∀ execution ∈ support ((simulateQ romImpl
          (verificationPhase keyResult.1.1 keyResult.1.2 prefixResult.1)).run prefixResult.2),
          execution.1.won = true →
          ¬ OutcomeBadEventOccurs execution.2 execution.1 .encoding →
          ¬ DecidingChainValueRevealed execution.2 execution.1 →
          ¬ Rom.AdaptiveFreshDigestCollisionWith keyResult.2 prefixResult.2
            (keygenStructuralTargetInput keyResult.1.2 keyResult.2) →
          Rom.AdaptiveFreshDigestCollisionWith prefixResult.2 execution.2
            (decidingTargetInput keyResult.1.2 keyResult.2 prefixResult.1.1.epoch
              (outcomeDecidingChain prefixResult.2
                ⟨keyResult.1.1, keyResult.1.2, prefixResult.1.1, prefixResult.1.2, false⟩)))
    (hcount : ∀ (leafIndex : LeafIndex) (message : Message) (signature : Signature)
        (chain : ChainIndex) (initialCache : QueryCache HashSpec),
        expectedSimulatedQueryCount romImpl
          (Rom.IsRelevantHashQuery fun input =>
            decidingTargetInput keyResult.1.2 keyResult.2 leafIndex chain input ≠ input)
          (Concrete.scheme.verify keyResult.1.1 leafIndex message signature) initialCache ≤ 40) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
        execution.1.won = true ∧ ¬ OutcomeBadEventOccurs execution.2 execution.1 .encoding ∧
          ¬ DecidingChainValueRevealed execution.2 execution.1 |
      (simulateQ romImpl (adversaryPhase adversary keyResult.1.1 keyResult.1.2 >>=
        verificationPhase keyResult.1.1 keyResult.1.2)).run keyResult.2] ≤
      (D : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
        (40 : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
  classical
  let event : GameOutcome × QueryCache HashSpec → Prop := fun execution =>
    execution.1.won = true ∧ ¬ OutcomeBadEventOccurs execution.2 execution.1 .encoding ∧
      ¬ DecidingChainValueRevealed execution.2 execution.1
  let collision : (Forgery × QueryLog SigningSpec) × QueryCache HashSpec → Prop :=
    fun prefixResult => Rom.AdaptiveFreshDigestCollisionWith keyResult.2 prefixResult.2
      (keygenStructuralTargetInput keyResult.1.2 keyResult.2)
  let adversaryRun := (simulateQ romImpl
    (adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run keyResult.2
  have hpointwise : ∀ prefixResult ∈ support adversaryRun,
      Pr[event | (simulateQ romImpl
          (verificationPhase keyResult.1.1 keyResult.1.2 prefixResult.1)).run prefixResult.2] ≤
        (if collision prefixResult then 1 else 0) +
          (40 : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
    intro prefixResult hprefix
    by_cases hcollision : collision prefixResult
    · rw [if_pos hcollision]
      exact le_add_right probEvent_le_one
    · rw [if_neg hcollision, zero_add]
      calc
        _ ≤ expectedSimulatedQueryCount romImpl
              (Rom.IsRelevantHashQuery fun input =>
                decidingTargetInput keyResult.1.2 keyResult.2 prefixResult.1.1.epoch
                  (outcomeDecidingChain prefixResult.2
                    ⟨keyResult.1.1, keyResult.1.2, prefixResult.1.1, prefixResult.1.2, false⟩)
                  input ≠ input)
              (verificationPhase keyResult.1.1 keyResult.1.2 prefixResult.1) prefixResult.2 /
              ((2 ^ digestBits : ℕ) : ℝ≥0∞) :=
          Rom.mixed_adaptiveFreshDigestCollisionWith_le_expected_moved _ _ _ event
            (fun execution hexecution hwin =>
              horient prefixResult hprefix (hcached prefixResult hprefix) execution hexecution
                hwin.1 hwin.2.1 hwin.2.2 hcollision)
        _ ≤ _ := by
          gcongr
          rw [expectedQueries_verificationPhase_eq]
          exact hcount _ _ _ _ _
  rw [simulateQ_bind, StateT.run_bind, probEvent_bind_eq_tsum]
  calc
    ∑' prefixResult, Pr[= prefixResult | adversaryRun] *
        Pr[event | (simulateQ romImpl
          (verificationPhase keyResult.1.1 keyResult.1.2 prefixResult.1)).run prefixResult.2] ≤
      ∑' prefixResult, Pr[= prefixResult | adversaryRun] *
        ((if collision prefixResult then 1 else 0) +
          (40 : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞)) := by
      apply ENNReal.tsum_le_tsum
      intro prefixResult
      by_cases hprefix : prefixResult ∈ support adversaryRun
      · gcongr
        exact hpointwise prefixResult hprefix
      · rw [probOutput_eq_zero_of_not_mem_support hprefix, zero_mul, zero_mul]
    _ = (∑' prefixResult, Pr[= prefixResult | adversaryRun] *
          (if collision prefixResult then 1 else 0)) +
        ∑' prefixResult, Pr[= prefixResult | adversaryRun] *
          ((40 : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞)) := by
      rw [← ENNReal.tsum_add]
      apply tsum_congr
      intro prefixResult
      rw [mul_add]
    _ ≤ _ := by
      gcongr
      · have hind : (∑' prefixResult, Pr[= prefixResult | adversaryRun] *
            (if collision prefixResult then 1 else 0)) = Pr[collision | adversaryRun] := by
          rw [probEvent_eq_tsum_ite]
          apply tsum_congr
          intro prefixResult
          split_ifs <;> simp
        rw [hind]
        calc
          Pr[collision | adversaryRun] ≤
              expectedSimulatedQueryCount romImpl
                (Rom.IsRelevantHashQuery fun input =>
                  keygenStructuralTargetInput keyResult.1.2 keyResult.2 input ≠ input)
                (adversaryPhase adversary keyResult.1.1 keyResult.1.2) keyResult.2 /
                ((2 ^ digestBits : ℕ) : ℝ≥0∞) :=
            Rom.mixed_adaptiveFreshDigestCollisionWith_le_expected_moved _ _ _ collision
              (fun _ _ h => h)
          _ ≤ _ := by
            gcongr
            exact expectedStructuralQueries_adversaryPhase_le adversary D hD _ _ _ _
      · exact Direct.tsum_probOutput_mul_le _ _ _ fun _ => le_rfl

/-! ## The second-lane bound -/

/-- The second lane: a winning run without encoding event and without a revealed deciding chain
value has probability at most `(D + 40) / 2^128`, given the orientation and the verifier count. -/
theorem decidingSecondLane_probability_le (adversary : Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D)
    (hcached : ∀ keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅),
      ∀ prefixResult ∈ support
        ((simulateQ romImpl (adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2),
        prefixResult.2 (Concrete.CacheView.encodingInput keyResult.1.2.parameter
          prefixResult.1.1.epoch
          (prefixResult.1.1.message, prefixResult.1.1.signature.randomness)) ≠ none)
    (horient : ∀ keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅),
      ∀ prefixResult ∈ support
        ((simulateQ romImpl (adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2),
        prefixResult.2 (Concrete.CacheView.encodingInput keyResult.1.2.parameter
          prefixResult.1.1.epoch
          (prefixResult.1.1.message, prefixResult.1.1.signature.randomness)) ≠ none →
        ∀ execution ∈ support ((simulateQ romImpl
          (verificationPhase keyResult.1.1 keyResult.1.2 prefixResult.1)).run prefixResult.2),
          execution.1.won = true →
          ¬ OutcomeBadEventOccurs execution.2 execution.1 .encoding →
          ¬ DecidingChainValueRevealed execution.2 execution.1 →
          ¬ Rom.AdaptiveFreshDigestCollisionWith keyResult.2 prefixResult.2
            (keygenStructuralTargetInput keyResult.1.2 keyResult.2) →
          Rom.AdaptiveFreshDigestCollisionWith prefixResult.2 execution.2
            (decidingTargetInput keyResult.1.2 keyResult.2 prefixResult.1.1.epoch
              (outcomeDecidingChain prefixResult.2
                ⟨keyResult.1.1, keyResult.1.2, prefixResult.1.1, prefixResult.1.2, false⟩)))
    (hcount : ∀ (secretKey : SecretKey) (cache : QueryCache HashSpec) (publicKey : PublicKey),
      publicKey.parameter = secretKey.parameter →
      ∀ (leafIndex : LeafIndex) (message : Message) (signature : Signature)
        (chain : ChainIndex) (initialCache : QueryCache HashSpec),
        expectedSimulatedQueryCount romImpl
          (Rom.IsRelevantHashQuery fun input =>
            decidingTargetInput secretKey cache leafIndex chain input ≠ input)
          (Concrete.scheme.verify publicKey leafIndex message signature) initialCache ≤ 40) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
        execution.1.won = true ∧ ¬ OutcomeBadEventOccurs execution.2 execution.1 .encoding ∧
          ¬ DecidingChainValueRevealed execution.2 execution.1 |
      detailedGameWithCache Concrete.scheme adversary] ≤
      ((D + 40 : ℕ) : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
  unfold detailedGameWithCache detailedGameCore
  simp only [detailedGameAfterKeygen_eq_phases]
  rw [simulateQ_bind, StateT.run_bind, probEvent_bind_eq_tsum, Nat.cast_add, ENNReal.add_div]
  apply tsum_probOutput_mul_le_of_mem_support
  intro keyResult hkeygen
  have hparameter := keygen_publicKey_parameter_eq keyResult hkeygen
  obtain ⟨⟨publicKey, secretKey⟩, keygenCache⟩ := keyResult
  exact decidingSecondLane_afterKeygen_le adversary D hD ((publicKey, secretKey), keygenCache)
    (hcached _ hkeygen) (horient _ hkeygen)
    (fun leafIndex message signature chain initialCache =>
      hcount secretKey keygenCache publicKey hparameter leafIndex message signature chain
        initialCache)

/-- The unconditional second-lane estimate for a syntactically bounded adversary. The added
encoding query fixes the deciding path before verification and leaves the game distribution
unchanged. -/
theorem decidingSecondLane_probability_le_direct (adversary : Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
        execution.1.won = true ∧ ¬ OutcomeBadEventOccurs execution.2 execution.1 .encoding ∧
          ¬ DecidingChainValueRevealed execution.2 execution.1 |
      detailedGameWithCache Concrete.scheme adversary] ≤
      ((D + 41 : ℕ) : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
  have hbound := decidingSecondLane_probability_le (Direct.withForgedEncodingQuery adversary)
    (D + 1) (Direct.withForgedEncodingQuery_isDirectQueryBound adversary D hD)
    (by
      intro keyResult hkeygen prefixResult hprefix
      have hparameter := keygen_publicKey_parameter_eq keyResult hkeygen
      rw [← hparameter]
      exact Direct.adversaryPhase_withForgedEncodingQuery_cached adversary keyResult.1.1
        keyResult.1.2 keyResult.2 prefixResult hprefix)
    (by
      intro keyResult hkeygen prefixResult hprefix hcached execution hafter hwin hencoding
        hrevealed hcollision
      exact deciding_afterKeygen_orientation _ keyResult hkeygen prefixResult hprefix hcached
        execution hafter hwin hencoding hrevealed hcollision)
    (by
      intro secretKey cache publicKey hparameter leafIndex message signature chain initialCache
      simpa only [decidingQueryBound_eq, Nat.cast_ofNat] using expectedSimulatedQueryCount_verify_deciding_le
        secretKey cache publicKey hparameter leafIndex message signature chain initialCache)
  rw [Direct.detailedGameWithCache_withForgedEncodingQuery] at hbound
  simpa only [Nat.add_assoc] using hbound

end XmssSecurity.Checksum.Deciding
