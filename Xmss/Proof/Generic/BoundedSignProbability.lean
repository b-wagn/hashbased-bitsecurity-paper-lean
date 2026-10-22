import Xmss.Proof.Generic.SignCacheHitProbability
import Xmss.Proof.Generic.StatementLemmas

open OracleComp OracleSpec ENNReal

namespace Xmss.Generic

variable [Code]

set_option maxRecDepth 100000

noncomputable def Signing.signBoundedAttemptsContinuation
    (attempts : Nat) (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message)
    (result : Option Signature × QueryCache HashSpec) :
    ProbComp (Option Signature × QueryCache HashSpec) :=
  match result.1 with
  | some signature => pure (some signature, result.2)
  | none => (simulateQ romImpl
      (Signing.signBoundedAttempts attempts secretKey leafIndex message)).run result.2

attribute [irreducible] Signing.signBoundedAttemptsContinuation

theorem Signing.signBoundedAttempts_run_succ_eq
    (attempts : Nat) (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message)
    (cache : QueryCache HashSpec) :
    (simulateQ romImpl
      (Signing.signBoundedAttempts (attempts + 1) secretKey leafIndex message)).run cache =
      (($ᵗ Randomness) >>= fun randomness =>
        (simulateQ randomOracle
          (Signing.signAttempt secretKey leafIndex message randomness :
            OracleComp HashSpec (Option Signature))).run cache >>=
          Signing.signBoundedAttemptsContinuation attempts secretKey leafIndex
            message) := by
  rw [Signing.signBoundedAttempts, simulateQ_bind, StateT.run_bind]
  have hsampleRun :
      (simulateQ romImpl
        (liftM Signing.signingRandomness)).run cache =
        (fun randomness => (randomness, cache)) <$> Signing.signingRandomness := by
    change (simulateQ (unifFwdImpl HashSpec +
        (randomOracle : QueryImpl HashSpec
          (StateT (QueryCache HashSpec) ProbComp)))
      (liftM Signing.signingRandomness)).run cache = _
    exact roSim.run_liftM
      (hashSpec := HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      Signing.signingRandomness cache
  rw [hsampleRun, Signing.signingRandomness_eq]
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
  apply bind_congr
  intro randomness
  rw [simulateQ_bind, StateT.run_bind]
  have hroute :
      simulateQ romImpl
          (liftM (Signing.signAttempt secretKey leafIndex message randomness :
            OracleComp HashSpec (Option Signature))) =
        simulateQ randomOracle
          (Signing.signAttempt secretKey leafIndex message randomness :
            OracleComp HashSpec (Option Signature)) := by
    change simulateQ (unifFwdImpl HashSpec + randomOracle)
        (liftM (Signing.signAttempt secretKey leafIndex message randomness :
          OracleComp HashSpec (Option Signature))) = _
    exact QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      (Signing.signAttempt secretKey leafIndex message randomness :
        OracleComp HashSpec (Option Signature))
  rw [hroute]
  apply bind_congr
  intro result
  rcases result with ⟨result, resultCache⟩
  cases result <;> simp [Signing.signBoundedAttemptsContinuation]

theorem Signing.signBoundedAttempts_run_succ_eq_sign_bind
    (attempts : Nat) (_publicKey : PublicKey) (secretKey : SecretKey)
    (leafIndex : LeafIndex) (message : Message) (cache : QueryCache HashSpec) :
    (simulateQ romImpl
      (Signing.signBoundedAttempts (attempts + 1) secretKey leafIndex message)).run cache =
      (simulateQ romImpl
        (Signing.sign secretKey leafIndex message)).run cache >>=
          Signing.signBoundedAttemptsContinuation attempts secretKey leafIndex
            message := by
  rw [Signing.signBoundedAttempts_run_succ_eq, Signing.sign_run_eq,
    bind_assoc]

end Xmss.Generic
