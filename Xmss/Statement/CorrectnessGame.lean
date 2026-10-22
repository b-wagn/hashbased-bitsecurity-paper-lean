import Xmss.Statement.UnforgeabilityGame

/-!
# Correctness Game

-/

open OracleComp OracleSpec ENNReal

namespace Xmss.Correctness

open Unforgeability SUFCMA

variable {ι : Type} {spec : OracleSpec ι} {PK SK Msg Sig : Type} {L : ℕ}

/-- An adaptive adversary with the public key and access to hashing, sampling, and signing. -/
structure Adversary {ι : Type} (spec : OracleSpec ι) (PK Msg Sig : Type) (L : ℕ) where
  main : PK → OracleComp (spec + SigningSpec Msg Sig L) Unit

/-- The request count, table `Signed`, and failure flag, over the ambient oracles. -/
abbrev Run (spec : OracleSpec ι) (Msg Sig : Type) (L : ℕ) : Type → Type :=
  AddWriterT ℕ (StateT (QueryLog (SigningSpec Msg Sig L) × Bool) (OracleComp spec))

/-- Count every request. At a fresh epoch, record and return the answer and flag signing or
verification failure. At a repeated epoch, return `none` without changing the record or flag. -/
def signingOracle (scheme : EpochBasedSignature spec PK SK Msg Sig L) (pk : PK) (sk : SK) :
    QueryImpl (SigningSpec Msg Sig L) (Run spec Msg Sig L) :=
  fun request => do
    AddWriterT.addTell 1
    let (signed, failed) ←
      liftM (get : StateT (QueryLog (SigningSpec Msg Sig L) × Bool) (OracleComp spec) _)
    if SigningTranscript.Signed signed request.epoch then
      return none
    else
      let answer ← liftM (scheme.sign sk request.epoch request.message)
      let verified ← liftM (match answer with
        | none => (pure false : OracleComp spec Bool)
        | some signature => scheme.verify pk request.epoch request.message signature)
      liftM (set (signed ++ [⟨request, answer⟩], failed || !verified) :
        StateT (QueryLog (SigningSpec Msg Sig L) × Bool) (OracleComp spec) Unit)
      return answer

/-- Generate keys and run the adversary; return the failure flag and request count. -/
def experiment (scheme : EpochBasedSignature spec PK SK Msg Sig L)
    (adversary : Adversary spec PK Msg Sig L) : OracleComp spec (Bool × ℕ) := do
  let (pk, sk) ← scheme.keygen
  let ((_, requests), (_, failed)) ←
    (simulateQ (QueryImpl.ofLift spec (Run spec Msg Sig L) + signingOracle scheme pk sk)
      (adversary.main pk)).run.run ([], false)
  return (failed, Multiplicative.toAdd requests)

variable {Input Output : Type} [DecidableEq Input] [SampleableType Output]

/-- The correctness experiment in the random-oracle model. -/
noncomputable def game
    (scheme : EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
    (adversary : Adversary (RandomOracleModel.World Input Output) PK Msg Sig L) :
    ProbComp (Bool × ℕ) :=
  RandomOracleModel.run (experiment scheme adversary)

/-- `Pr[CORRECT_SIG(A) = 1]`. -/
noncomputable def advantage
    (scheme : EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
    (adversary : Adversary (RandomOracleModel.World Input Output) PK Msg Sig L) : ℝ≥0∞ :=
  Pr[fun result => result.1 = true | game scheme adversary]

/-- The adversary makes at most `q` signing queries, with probability 1. -/
def HasRequestBound
    (scheme : EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
    (adversary : Adversary (RandomOracleModel.World Input Output) PK Msg Sig L) (q : ℕ) : Prop :=
  Pr[fun result => result.2 ≤ q | game scheme adversary] = 1

/-- At most `δ · q` failure probability for every adversary with at most `q` signing requests. -/
def HasCorrectnessError
    (scheme : EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
    (δ : ℝ≥0∞) : Prop :=
  ∀ q adversary, HasRequestBound scheme adversary q → advantage scheme adversary ≤ δ * q

end Xmss.Correctness
