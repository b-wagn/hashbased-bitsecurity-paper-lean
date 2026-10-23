import Xmss.Proof.Checksum.HiddenSibling.Signed
import Xmss.Proof.Checksum.HiddenSibling.SignedLane
import Xmss.Proof.Checksum.HiddenSibling.SignerBridge
import Xmss.Proof.Checksum.Direct.SharedDecidingBudget
import Xmss.Proof.Generic.Direct.DecidingFirstLaneBridge
import Xmss.Proof.Checksum.Code
import Xmss.Proof.Checksum.EncodingProbability
/-! A budget of one request permits either signing without direct hashing or hashing without
signing. Signed executions agree with the adversary obtained by suppressing all direct hashes.
The exact advantage bound is assembled in `ExactThreeBudget.lean`. -/

open OracleComp OracleSpec ENNReal
open Xmss.Generic

set_option backward.isDefEq.respectTransparency false

namespace Xmss.Checksum.HiddenSibling

/-- The adversary with every direct hash query answered by `default` without querying. -/
noncomputable def hashFree (adversary : Adversary) : Adversary :=
  ⟨fun publicKey => Direct.pruneDirect 0 (adversary.main publicKey)⟩

theorem probEvent_game_phases (adversary : Adversary)
    (event : GameOutcome × QueryCache HashSpec → Prop) :
    Pr[event | detailedGameWithCache precomputedScheme adversary] =
      ∑' keyResult, Pr[= keyResult | (simulateQ romImpl precomputedScheme.keygen).run ∅] *
        ∑' prefixResult, Pr[= prefixResult |
            realRun keyResult.1.2 (adversary.main keyResult.1.1) keyResult.2] *
          Pr[event | (simulateQ romImpl (Deciding.verificationPhase keyResult.1.1 keyResult.1.2
            prefixResult.1)).run prefixResult.2] := by
  unfold detailedGameWithCache detailedGameCore
  simp only [Deciding.detailedGameAfterKeygen_eq_phases]
  rw [simulateQ_bind, StateT.run_bind, probEvent_bind_eq_tsum]
  refine tsum_congr fun keyResult => congrArg _ ?_
  rw [simulateQ_bind, StateT.run_bind, probEvent_bind_eq_tsum]
  rfl

/-- When a request can only come first, the winning executions with a request are those of the
hash-free adversary. -/
theorem signed_won_eq_hashFree (adversary : Adversary)
    (hweighted : ∀ publicKey, IsWeightedBound 3 (adversary.main publicKey) 3) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
        execution.1.won = true ∧ execution.1.signingLog ≠ [] |
      detailedGameWithCache precomputedScheme adversary] =
      Pr[fun execution : GameOutcome × QueryCache HashSpec =>
          execution.1.won = true ∧ execution.1.signingLog ≠ [] |
        detailedGameWithCache precomputedScheme (hashFree adversary)] := by
  rw [probEvent_game_phases, probEvent_game_phases]
  refine tsum_congr fun keyResult => congrArg _ (tsum_congr fun prefixResult => ?_)
  by_cases hsigned : prefixResult.1.2 ≠ []
  · congr 1
    have h := probEvent_realRun_sign_eq keyResult.1.2 3 3 (adversary.main keyResult.1.1)
      (hweighted keyResult.1.1) le_rfl keyResult.2 (· = prefixResult)
    rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
    calc
      _ = Pr[fun result => result = prefixResult ∧ result.1.2 ≠ [] |
            realRun keyResult.1.2 (adversary.main keyResult.1.1) keyResult.2] :=
        probEvent_congr' (fun result _ => ⟨fun heq => ⟨heq, heq ▸ hsigned⟩, fun h => h.1⟩) rfl
      _ = _ := h
      _ = _ := probEvent_congr' (fun result _ => ⟨fun h => h.1, fun heq => ⟨heq, heq ▸ hsigned⟩⟩)
        rfl
  · have hzero : ∀ secretKey publicKey,
        Pr[fun execution : GameOutcome × QueryCache HashSpec =>
            execution.1.won = true ∧ execution.1.signingLog ≠ [] |
          (simulateQ romImpl (Deciding.verificationPhase publicKey secretKey prefixResult.1)).run
            prefixResult.2] = 0 := fun secretKey publicKey =>
      probEvent_eq_zero fun execution hexecution hevent => hsigned (by
        rw [← (Deciding.verificationPhase_support _ _ _ _ _ hexecution).2.2.2.1]
        exact hevent.2)
    simp only [hzero, mul_zero]

/-! ## The executions without a request -/

/-- A predicate at the top address never holds for an encoding input. -/
theorem not_top_encodingInput (parameter : PublicParameter) (leafIndex : LeafIndex)
    (payload : Message × Randomness) :
    ¬ AtHashAddress parameter (.merkle topLevel Generic.Merkle.rootNode)
      (CacheView.encodingInput parameter leafIndex payload) := by
  simp [CacheView.encodingInput]

/-- The expected number of requests in the forwarded run. -/
noncomputable def signRate (adversary : Adversary) (publicKey : PublicKey) : ℝ≥0∞ :=
  expectedSimulatedQueryCount idealImpl IsSignQuery (adversary.main publicKey) ∅

end Xmss.Checksum.HiddenSibling
