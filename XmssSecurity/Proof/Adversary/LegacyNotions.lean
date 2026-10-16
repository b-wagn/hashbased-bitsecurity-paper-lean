import XmssSecurity.Statement.Security.SUFCMA
import XmssSecurity.Proof.Legacy.PerModeNotionsEUFCMA

/-!
# The two original counting notions

The existing proofs were written against two notions: `notionTotal`, charging every hash call of
the experiment at the level of the random-oracle implementation (`RandomOracleModel.experiment`),
and `notionDirect`, charging only the adversary's own hash calls inside the game
(`gameCountedDirect`). The statement now has one notion per counting mode (`SUFCMA.notion`);
`Proof/Modes/` shows that `notion CountingMode.allHashes` is `notionTotal` and
`notion CountingMode.direct` is `notionDirect`, so the existing proofs carry over.
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

namespace RandomOracleModel

variable (Input Output : Type) [DecidableEq Input] [SampleableType Output]

/-- As `impl`, additionally charging one unit per hash call, including cache hits, and nothing
per uniform sample. -/
noncomputable def countedImpl :=
  (impl Input Output).withAddCost (hashCost Input Output)

variable {Input Output}

/-- Run a computation of the random-oracle world from an empty cache; return its result and the
total number of hash calls. -/
noncomputable def experiment {α : Type} (computation : OracleComp (World Input Output) α) :
    ProbComp (α × ℕ) :=
  (simulateQ (countedImpl Input Output) computation).run.run' ∅

end RandomOracleModel

namespace SUFCMA

variable {ι : Type} {spec : OracleSpec ι} {PK SK Msg Sig : Type} {L : ℕ}

/-- The experiment as `game`, additionally charging the adversary's own queries to the ambient
oracles by `cost`. Signing requests cost nothing, and neither do the hash calls of key generation,
of the signer, or of the final verification. -/
def gameCountedDirect [DecidableEq Msg] [DecidableEq Sig] (cost : spec.Domain → ℕ)
    (scheme : EpochBasedSignature spec PK SK Msg Sig L)
    (adversary : Adversary spec PK Msg Sig L) : OracleComp spec (Bool × ℕ) := do
  let (pk, sk) ← scheme.keygen
  let (((forgery, charged), log) :
      (Forgery Msg Sig L × Multiplicative ℕ) × QueryLog (SigningSpec Msg Sig L)) ←
    (simulateQ
      ((QueryImpl.ofLift spec (WriterT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec)) +
          signingOracle scheme sk).withAddCost (fun | .inl input => cost input | .inr _ => 0))
      (adversary.main pk)).run.run
  let verified ← scheme.verify pk forgery.epoch forgery.message forgery.signature
  return (decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified,
    Multiplicative.toAdd charged)

variable {Input Output : Type} [DecidableEq Input] [SampleableType Output]

/-- SUF-CMA in the random-oracle model, charging every hash call of the experiment. -/
noncomputable def notionTotal [DecidableEq Msg] [DecidableEq Sig] :
    SecurityNotion
      (EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L) where
  Adversary := Adversary (RandomOracleModel.World Input Output) PK Msg Sig L
  experiment := fun scheme adversary => RandomOracleModel.experiment (game scheme adversary)

/-- SUF-CMA in the random-oracle model, charging only the adversary's own hash calls. -/
noncomputable def notionDirect [DecidableEq Msg] [DecidableEq Sig] :
    SecurityNotion
      (EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L) where
  Adversary := Adversary (RandomOracleModel.World Input Output) PK Msg Sig L
  experiment := fun scheme adversary =>
    RandomOracleModel.run (gameCountedDirect (fun | .inl _ => 0 | .inr _ => 1) scheme adversary)

end SUFCMA

end XmssSecurity
