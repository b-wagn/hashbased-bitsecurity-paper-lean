import Xmss.Proof.TargetSum.SigningFailure
import Xmss.Proof.Common.CorrectnessRequests
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-!
# The correctness error of the target-sum scheme

The correctness experiment sets its flag only if all `K` trials of some signing request fail
(`experiment_flag_signingFails`). A request is determined by the public parameter, the master
seed, the epoch, and the message, so a union bound over these `2^672` tuples and the bound
`2^-(2^16)` of `probEvent_signingFails_le` give the internal bound `2^-64864`
(`correctnessError_le`). `correctnessError_paper` gives the paper's stated bound `2^-256`.
-/

open OracleComp OracleSpec ENNReal

open Xmss.Generic

namespace Xmss.TargetSum.Correctness

/-- The union bound over a finite type. -/
theorem probEvent_exists_le_sum {ι α : Type} [Fintype ι] (computation : ProbComp α)
    (event : ι → α → Prop) :
    Pr[fun result => ∃ index, event index result | computation] ≤
      ∑ index, Pr[event index | computation] :=
  (probEvent_mono'' fun _ ⟨index, hindex⟩ => ⟨index, Finset.mem_univ index, hindex⟩).trans
    (probEvent_exists_finset_le_sum Finset.univ computation event)

/-- Whatever the adversary queries, the correctness experiment sets its flag with probability at
most `2^-64864`: the flag shows all trials of some request failing, and a union bound over the
`2^672` public parameters, master seeds, epochs and messages loses `672` of the `2^16` bits of
`probEvent_signingFails_le`. -/
theorem advantage_le
    (adversary : Correctness.Adversary OracleWorld PublicKey Message Generic.Signature lifetime) :
    Correctness.advantage Generic.xmss adversary ≤ 1 / 2 ^ 64864 := by
  unfold Correctness.advantage Correctness.game RandomOracleModel.run
  rw [← AdversaryBridge.romImpl_eq, StateT.run'_eq, probEvent_map]
  calc
    _ ≤ _ := probEvent_flag_le_exists_signingFails adversary
    _ ≤ ∑ request : PublicParameter × MasterSeed × LeafIndex × Message,
        Pr[fun result => SigningFails request.1 request.2.1 request.2.2.1 request.2.2.2 result.2 |
          (simulateQ romImpl (Correctness.experiment Generic.xmss adversary)).run ∅] :=
      (probEvent_mono'' fun _ ⟨parameter, seed, leafIndex, message, hfails⟩ =>
        ⟨(parameter, seed, leafIndex, message), hfails⟩).trans (probEvent_exists_le_sum _ _)
    _ ≤ ∑ _request : PublicParameter × MasterSeed × LeafIndex × Message,
        ((1 : ℝ≥0∞) / 2) ^ (2 ^ 16) :=
      Finset.sum_le_sum fun request _ => probEvent_signingFails_le _ _ _ _ _
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, card_requestTuples, nsmul_eq_mul, Nat.cast_pow,
        Nat.cast_ofNat, union_numeric]

/-- The target-sum scheme has correctness error at most `2^-64864`. An adversary without signing
queries never sets the flag. -/
theorem correctnessError_le : Correctness.HasCorrectnessError Generic.xmss (1 / 2 ^ 64864) := by
  intro q adversary hbound
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · rw [Correctness.advantage_eq_zero_of_noRequests Generic.xmss adversary hbound]
    exact zero_le
  · calc
      _ ≤ 1 / 2 ^ 64864 := advantage_le adversary
      _ = 1 / 2 ^ 64864 * 1 := (mul_one _).symm
      _ ≤ _ := by gcongr; exact_mod_cast hq

/-- The paper's correctness bound, obtained from the stronger internal estimate. -/
theorem correctnessError_paper : Correctness.HasCorrectnessError Generic.xmss (1 / 2 ^ 256) := by
  intro q adversary hbound
  refine (correctnessError_le q adversary hbound).trans ?_
  gcongr <;> norm_num

end Xmss.TargetSum.Correctness
