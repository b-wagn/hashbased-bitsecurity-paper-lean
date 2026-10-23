import SlhDsaSecurity.Statement.Scheme
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.QueryTracking.CostModel

/-!
# The verifier-counted SLH-DSA experiment

The adversary has private randomness, the shared byte random oracle, and adaptive
signing access. Every signing request runs the signer and counts once, including
repetitions and invalid contexts. Key-generation and signing hashes are free.
Direct adversary hashes and every call in final verification count, including
repeated inputs. There is no verification oracle or restriction on private work.

The lifetime and work restrictions are almost-sure bounds on this experiment,
not expected bounds and not an oracle that silently refuses excess requests.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.Security

abbrev SigningSpec : OracleSpec Message := Message →ₒ Option Bytes
abbrev SigningLog := QueryLog SigningSpec

structure Forgery where
  message : Message
  signature : Bytes
deriving DecidableEq

structure Adversary where
  main : PublicKey → OracleComp (OracleWorld + SigningSpec) Forgery

inductive QueryKind where
  | signing | hash | verification
deriving DecidableEq, Fintype

abbrev Counts := QueryKind → Nat

def Counts.single (kind : QueryKind) (count : Nat) : Counts := Pi.single kind count

/-- The two hash-query sources charged to q. -/
def Counts.work (counts : Counts) : Nat := counts .hash + counts .verification

abbrev CountedRun := AddWriterT Counts (StateT SigningLog (OracleComp OracleWorld))

def hashCost : OracleWorld.Domain → Nat :=
  Xmss.RandomOracleModel.hashCost Bytes HashOutput

def countQueries {α : Type} (cost : OracleWorld.Domain → Counts)
    (computation : OracleComp OracleWorld α) : OracleComp OracleWorld (α × Counts) :=
  (fun result => (result.1, Multiplicative.toAdd result.2)) <$>
    (simulateQ (addCostOracle cost) computation).run

/-- Count every request and record its answer, without rejecting repeated messages. -/
def signingOracle (sk : SecretKey) : QueryImpl SigningSpec CountedRun := fun request => do
  AddWriterT.addTell (Counts.single .signing 1)
  let answer ← liftM (Scheme.sign sk request : OracleComp OracleWorld (Option Bytes))
  liftM (modify (fun signed => signed ++ [⟨request, answer⟩]) :
    StateT SigningLog (OracleComp OracleWorld) Unit)
  return answer

structure Outcome where
  forgery : Forgery
  signed : SigningLog
  verified : Bool
  counts : Counts

/-- One common transcript and verification run for SUF-CMA and EUF-CMA. -/
noncomputable def experiment (adversary : Adversary) : OracleComp OracleWorld Outcome := do
  let (sk, pk) ← Scheme.keygen
  let ((forgery, adversaryCounts), signed) ←
    (simulateQ
      ((QueryImpl.ofLift OracleWorld (StateT SigningLog (OracleComp OracleWorld))).withAddCost
          (fun input => Counts.single .hash (hashCost input)) + signingOracle sk)
      (adversary.main pk)).run.run []
  let (verified, verifierCounts) ← countQueries
    (fun input => Counts.single .verification (hashCost input))
    (Scheme.verify pk forgery.message forgery.signature)
  return {
    forgery := forgery
    signed := signed
    verified := verified
    counts := Multiplicative.toAdd adversaryCounts + verifierCounts }

/-- All parties share one consistent oracle, initially empty. -/
noncomputable def run (adversary : Adversary) : ProbComp Outcome :=
  Xmss.RandomOracleModel.run (experiment adversary)

inductive Notion where
  | strong | standard

/-- Strong freshness excludes returned pairs; standard freshness excludes all requested messages. -/
def Fresh : Notion → SigningLog → Forgery → Prop
  | .strong, signed, forgery =>
      ¬∃ entry ∈ signed, entry.1 = forgery.message ∧ entry.2 = some forgery.signature
  | .standard, signed, forgery => ¬∃ entry ∈ signed, entry.1 = forgery.message

def Wins (notion : Notion) (outcome : Outcome) : Prop :=
  outcome.verified = true ∧ Fresh notion outcome.signed outcome.forgery

noncomputable def advantage (notion : Notion) (adversary : Adversary) : ℝ≥0∞ :=
  Pr[Wins notion | run adversary]

/-! ## Counting every hash call in the game

The verifier-counted experiment above leaves key generation and signing free. The
statements below instead charge **every** hash call made anywhere in the game — key
generation, signing, the adversary's direct calls, and final verification — matching the
all-hashes accounting of the leanVM `lean_sphincs` statement. Signing requests are still
capped separately at `signingLimit`, including repetitions and failures.
-/

/-- Charge one unit for every hash call in the whole computation. -/
def countAllHashes {α : Type} (computation : OracleComp OracleWorld α) :
    OracleComp OracleWorld (α × Nat) :=
  (fun result => (result.1, Multiplicative.toAdd result.2)) <$>
    (simulateQ (addCostOracle hashCost) computation).run

/-- The same experiment, instrumented with the total hash count. -/
noncomputable def runAll (adversary : Adversary) : ProbComp (Outcome × Nat) :=
  Xmss.RandomOracleModel.run (countAllHashes (experiment adversary))

noncomputable def totalAdvantage (notion : Notion) (adversary : Adversary) : ℝ≥0∞ :=
  Pr[fun result => Wins notion result.1 | runAll adversary]

end SlhDsaSecurity.Security
