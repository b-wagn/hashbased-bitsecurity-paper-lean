import SlhDsaSecurity.Proof.Correctness.Scheme
import SlhDsaSecurity.Proof.Correctness.Naturality

/-!
# Correctness with one shared lazy random oracle

The experiment runs the actual key generator, signer, and byte-facing verifier. All three
share the same cache; the three key-generation seeds are private independent uniform samples.
Invalid contexts produce `none`; every valid context produces `some true` with probability one.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.Correctness.SharedROM

section Algorithms

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- Keep framing rejection distinct from a signature that fails verification. -/
def signAndVerify (keys : SecretKey × PublicKey) (request : Message) : m (Option Bool) := do
  match ← SlhDsaSecurity.Scheme.sign keys.1 request with
  | none => return none
  | some signature => return some (← SlhDsaSecurity.Scheme.verify keys.2 request signature)

def roundTrip (secretSeed prfSeed publicSeed : Digest) (request : Message) : m (Option Bool) := do
  let keys ← SlhDsaSecurity.Scheme.keygenInternal secretSeed prfSeed publicSeed
  signAndVerify keys request

end Algorithms

/-- Use actual randomized key generation, including its three private uniform samples. -/
noncomputable def experiment (request : Message) : OracleComp OracleWorld (Option Bool) := do
  let keys ← SlhDsaSecurity.Scheme.keygen
  signAndVerify keys request

theorem roundTrip_fixed [HasQuery HashSpec Id]
    (secretSeed prfSeed publicSeed : Digest) (request : Message) :
    roundTrip (m := Id) secretSeed prfSeed publicSeed request =
      request.frame.map (fun _ => true) := by
  simp only [roundTrip, bind]
  cases hframe : request.frame with
  | none => simp only [signAndVerify, SlhDsaSecurity.Scheme.sign, hframe, bind, pure, Option.map_none]
  | some message =>
      obtain ⟨signature, hsign, hverify⟩ := Scheme.verify_sign
        (SlhDsaSecurity.Scheme.keygenInternal (m := Id) secretSeed prfSeed publicSeed).1
        request message hframe rfl
      change SlhDsaSecurity.Scheme.verify (m := Id)
        (SlhDsaSecurity.Scheme.keygenInternal (m := Id) secretSeed prfSeed publicSeed).2
        request signature = true at hverify
      simp only [signAndVerify, hsign, bind, hverify, pure, Option.map_some]

section Naturality

variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable (impl : QueryImpl HashSpec m) [HasQuery HashSpec m]
variable (himpl : ∀ input, impl input = (query (spec := HashSpec) input : m HashOutput))
include himpl

theorem signAndVerify_simulate (keys : SecretKey × PublicKey) (request : Message) :
    simulateQ impl (signAndVerify keys request) =
      (signAndVerify keys request : m (Option Bool)) := by
  simp only [signAndVerify, simulateQ_bind, Naturality.sign_simulate impl himpl]
  congr 1
  funext answer
  cases answer with
  | none => exact simulateQ_pure impl none
  | some signature =>
      simp only [simulateQ_bind, simulateQ_pure, VerifierNaturality.verify_simulate impl himpl]

theorem roundTrip_simulate (secretSeed prfSeed publicSeed : Digest) (request : Message) :
    simulateQ impl (roundTrip secretSeed prfSeed publicSeed request) =
      (roundTrip secretSeed prfSeed publicSeed request : m (Option Bool)) := by
  simp only [roundTrip, simulateQ_bind, Naturality.keygenInternal_simulate impl himpl,
    signAndVerify_simulate impl himpl]

end Naturality

theorem roundTrip_probability_one (secretSeed prfSeed publicSeed : Digest) (request : Message)
    (cache : QueryCache HashSpec) :
    Pr[fun result => result = request.frame.map (fun _ => true) |
      (simulateQ randomOracle
        (roundTrip secretSeed prfSeed publicSeed request : OracleComp HashSpec (Option Bool))).run' cache] = 1 := by
  rw [StateT.run'_eq, probEvent_map]
  apply (probEvent_eq_one_simulateQ_randomOracle_run_iff
    (roundTrip secretSeed prfSeed publicSeed request : OracleComp HashSpec (Option Bool))
    cache (fun result => result = request.frame.map (fun _ => true))).mpr
  intro fixedHash _
  letI : HasQuery HashSpec Id := ⟨fixedHash⟩
  change simulateQ fixedHash
      (roundTrip secretSeed prfSeed publicSeed request : OracleComp HashSpec (Option Bool)) = _
  rw [roundTrip_simulate fixedHash (fun _ => rfl)]
  exact roundTrip_fixed _ _ _ _

theorem roundTrip_lift (secretSeed prfSeed publicSeed : Digest) (request : Message) :
    (roundTrip secretSeed prfSeed publicSeed request : OracleComp OracleWorld (Option Bool)) =
      OracleComp.liftComp
        (roundTrip secretSeed prfSeed publicSeed request : OracleComp HashSpec (Option Bool))
        OracleWorld := by
  exact (roundTrip_simulate
    (fun input => query (spec := HashSpec) input : QueryImpl HashSpec (OracleComp OracleWorld))
    (fun _ => rfl) secretSeed prfSeed publicSeed request).symm

theorem experiment_run (request : Message) (cache : QueryCache HashSpec) :
    (simulateQ (XmssSecurity.RandomOracleModel.impl Bytes HashOutput) (experiment request)).run' cache =
      (do
        let secretSeed ← ($ᵗ Digest : ProbComp Digest)
        let prfSeed ← ($ᵗ Digest : ProbComp Digest)
        let publicSeed ← ($ᵗ Digest : ProbComp Digest)
        (simulateQ randomOracle
          (roundTrip secretSeed prfSeed publicSeed request : OracleComp HashSpec (Option Bool))).run' cache) := by
  simp only [experiment, SlhDsaSecurity.Scheme.keygen, bind_assoc]
  change (simulateQ (XmssSecurity.RandomOracleModel.impl Bytes HashOutput)
    (do
      let secretSeed ← liftM ($ᵗ Digest : ProbComp Digest)
      let prfSeed ← liftM ($ᵗ Digest : ProbComp Digest)
      let publicSeed ← liftM ($ᵗ Digest : ProbComp Digest)
      roundTrip secretSeed prfSeed publicSeed request)).run' cache = _
  simp only [XmssSecurity.RandomOracleModel.impl, simulateQ_bind,
    roSim.run'_liftM_bind, roundTrip_lift, QueryImpl.simulateQ_add_liftComp_right]

/-- Actual private seed generation and all honest algorithms use the same shared oracle. -/
theorem experiment_probability_one (request : Message) (cache : QueryCache HashSpec) :
    Pr[fun result => result = request.frame.map (fun _ => true) |
      (simulateQ (XmssSecurity.RandomOracleModel.impl Bytes HashOutput)
        (experiment request)).run' cache] = 1 := by
  rw [experiment_run]
  simp_rw [probEvent_bind_eq_tsum, roundTrip_probability_one, mul_one,
    tsum_probOutput_of_liftM_PMF]
  simp only [mul_one, tsum_probOutput_of_liftM_PMF]

theorem valid_context_probability_one (request : Message)
    (hcontext : request.context.length ≤ 255) :
    Pr[fun result => result = some true |
      XmssSecurity.RandomOracleModel.run (experiment request)] = 1 := by
  simpa only [XmssSecurity.RandomOracleModel.run, Message.frame, if_pos hcontext, Option.map_some] using
    experiment_probability_one request ∅

theorem invalid_context_probability_one (request : Message)
    (hcontext : 255 < request.context.length) :
    Pr[fun result => result = none |
      XmssSecurity.RandomOracleModel.run (experiment request)] = 1 := by
  simpa only [XmssSecurity.RandomOracleModel.run, Message.frame, if_neg (by omega : ¬ request.context.length ≤ 255), Option.map_none] using
    experiment_probability_one request ∅

end SlhDsaSecurity.Correctness.SharedROM
