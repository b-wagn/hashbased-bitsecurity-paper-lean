import XmssSecurity.Statement.SynchronizedSignature
import XmssSecurity.Statement.RandomOracleModel
import XmssSecurity.Statement.BitSecurity
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.QueryTracking.CostModel

/-!
# Strong unforgeability under chosen-message attacks

The synchronized security experiment `SY-UF-CMA` of Definition 8 of eprint 2025/055 (which is
strong unforgeability, Remark 2 there), for a synchronized signature scheme in the random-oracle
model:

1. the game generates `(pk, sk) ← Gen` and runs the adversary on `pk`;
2. the adversary may query the hash oracle, sample privately, and request signatures `(ep, m)`;
   every request is answered by `Sig(sk, ep, m)` and recorded;
3. the adversary outputs a forgery `(ep*, m*, σ*)` and wins if `Ver(pk, ep*, m*, σ*) = 1`, the
   signer never answered the request `(ep*, m*)` with `σ*`, and no epoch was requested twice.

The adversary has no verification oracle; the only verification is the game's final check.

The paper's signing oracle refuses a second request for an epoch; here a repeated epoch is still
answered (the adversary learns one more signature), but such a transcript invalidates the forgery
(`SigningTranscript.Valid`). The two formulations are equivalent for the bit-security claim. An
adversary of the paper's game becomes one of this game by answering a repeated request with
`none` locally instead of forwarding it: the transcript stays valid, no query is added, and the
winning probability is unchanged. An adversary of this game becomes one of the paper's game by
forwarding every request: once it repeats an epoch it cannot win here, and whatever it does in
the paper's game only helps.

## Counting modes

The number `q` of queries charged to the adversary always includes its own hash calls, one unit
per call also for a repeated input. A `CountingMode` says which of the following are charged in
addition: the hash calls of key generation, the hash calls of the signer while answering signing
requests, the hash calls of the final verification of the forgery, and one unit per signing
request. This gives sixteen notions `notion mode`, one `SecurityNotion` per mode. `direct`
charges nothing extra: the same bound must hold against adversaries whose own work is small,
whatever the honest parties compute. `allHashes` charges every hash call of the experiment.
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.SUFCMA

/-- A signing request: an epoch and a message. -/
structure SignRequest (Msg : Type) (L : ℕ) where
  epoch : Fin L
  message : Msg
deriving DecidableEq

/-- A claimed forgery: an epoch, a message, and a signature. -/
structure Forgery (Msg Sig : Type) (L : ℕ) where
  epoch : Fin L
  message : Msg
  signature : Sig
deriving DecidableEq

variable {Msg Sig : Type} {L : ℕ}

/-- The request a forgery claims to answer. -/
def Forgery.request (forgery : Forgery Msg Sig L) : SignRequest Msg L :=
  ⟨forgery.epoch, forgery.message⟩

/-- The signing oracle answers a request by a signature, or `none` if the signer fails. -/
abbrev SigningSpec (Msg Sig : Type) (L : ℕ) : OracleSpec (SignRequest Msg L) :=
  SignRequest Msg L →ₒ Option Sig

namespace SigningTranscript

/-- No epoch is requested twice. The adversary may request signatures adaptively, but a transcript
with two requests at the same epoch cannot win. -/
def Valid (log : QueryLog (SigningSpec Msg Sig L)) : Prop :=
  (log.map fun entry => entry.1.epoch).Nodup

instance (log : QueryLog (SigningSpec Msg Sig L)) : Decidable (Valid log) :=
  inferInstanceAs (Decidable ((log.map fun entry => entry.1.epoch).Nodup))

/-- The signer answered the forgery's request with the forgery's signature. A different signature
for a requested epoch and message is therefore a valid strong forgery. -/
def Contains [DecidableEq Msg] [DecidableEq Sig] (log : QueryLog (SigningSpec Msg Sig L))
    (forgery : Forgery Msg Sig L) : Prop :=
  ∃ entry ∈ log, entry.1 = forgery.request ∧ entry.2 = some forgery.signature

instance [DecidableEq Msg] [DecidableEq Sig] (log : QueryLog (SigningSpec Msg Sig L))
    (forgery : Forgery Msg Sig L) : Decidable (Contains log forgery) :=
  inferInstanceAs
    (Decidable (∃ entry ∈ log, entry.1 = forgery.request ∧ entry.2 = some forgery.signature))

end SigningTranscript

/-- Which queries of the experiment are charged to the adversary in addition to its own hash
calls, which are always charged. -/
structure CountingMode where
  /-- Charge the hash calls of key generation. -/
  keygen : Bool
  /-- Charge the hash calls of the signer while answering the adversary's signing requests. -/
  signer : Bool
  /-- Charge the hash calls of the final verification of the forgery. -/
  verifier : Bool
  /-- Charge one unit per signing request. -/
  requests : Bool
deriving DecidableEq, Repr

namespace CountingMode

/-- Only the adversary's own hash calls. -/
def direct : CountingMode := ⟨false, false, false, false⟩

/-- Every hash call of the experiment: key generation, the adversary, the signer, and the
verification of the forgery. -/
def allHashes : CountingMode := ⟨true, true, true, false⟩

/-- Every hash call of the experiment and every signing request. -/
def everything : CountingMode := ⟨true, true, true, true⟩

end CountingMode

variable {ι : Type} {spec : OracleSpec ι} {PK SK : Type}

/-- The cost `cost` if `charged`, and the zero cost otherwise. -/
def costIf (charged : Bool) (cost : spec.Domain → ℕ) : spec.Domain → ℕ :=
  if charged then cost else fun _ => 0

/-- Run a computation and return its result together with the sum of `cost` over the queries it
made. -/
def charge {α : Type} (cost : spec.Domain → ℕ) (computation : OracleComp spec α) :
    OracleComp spec (α × ℕ) :=
  (fun result => (result.1, Multiplicative.toAdd result.2)) <$>
    (simulateQ (addCostOracle cost) computation).run

/-- An adaptive adversary: given the public key, it may use the ambient oracles and the signing
oracle, and returns a claimed forgery. -/
structure Adversary {ι : Type} (spec : OracleSpec ι) (PK Msg Sig : Type) (L : ℕ) where
  main : PK → OracleComp (spec + SigningSpec Msg Sig L) (Forgery Msg Sig L)

/-- The signing oracle: answer by the scheme's signer and record the request and answer. -/
def signingOracle (scheme : SynchronizedSignature spec PK SK Msg Sig L) (sk : SK) :
    QueryImpl (SigningSpec Msg Sig L)
      (WriterT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec)) :=
  QueryImpl.withLogging fun request => scheme.sign sk request.epoch request.message

/-- The experiment, before any accounting: key generation, the adversary with the ambient oracles
forwarded and the logged signing oracle, and verification of the forgery. The notions are stated
with `gameCounted`, which adds the accounting; `Proof/Modes/` shows that `gameCounted` projects
to `game` in every mode. -/
def game [DecidableEq Msg] [DecidableEq Sig]
    (scheme : SynchronizedSignature spec PK SK Msg Sig L)
    (adversary : Adversary spec PK Msg Sig L) : OracleComp spec Bool := do
  let (pk, sk) ← scheme.keygen
  let ((forgery, log) : Forgery Msg Sig L × QueryLog (SigningSpec Msg Sig L)) ←
    (simulateQ
      (QueryImpl.ofLift spec (WriterT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec)) +
        signingOracle scheme sk)
      (adversary.main pk)).run
  let verified ← scheme.verify pk forgery.epoch forgery.message forgery.signature
  return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified

/-- The monad of the adversary's run in `gameCounted`: the charged units, the signing log, and
the ambient oracles. -/
abbrev ChargedRun (spec : OracleSpec ι) (Msg Sig : Type) (L : ℕ) : Type → Type :=
  AddWriterT ℕ (WriterT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec))

/-- The signing oracle of `gameCounted`: as `signingOracle`, additionally charging the signer's
queries by `signerCost` and `requestCost` units per request. -/
def signingOracleCounted (signerCost : spec.Domain → ℕ) (requestCost : ℕ)
    (scheme : SynchronizedSignature spec PK SK Msg Sig L) (sk : SK) :
    QueryImpl (SigningSpec Msg Sig L) (ChargedRun spec Msg Sig L) :=
  fun request => do
    let (answer, charged) ← liftM (charge signerCost (scheme.sign sk request.epoch request.message))
    AddWriterT.addTell (M := WriterT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec))
      (requestCost + charged)
    liftM (tell [⟨request, answer⟩] : WriterT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec) Unit)
    return answer

/-- The experiment as `game`, additionally returning the number of queries charged to the
adversary under `mode`: its own queries to the ambient oracles at `cost`, and, as the mode says,
the queries of key generation at `cost`, the queries of the signer at `cost`, the queries of the
final verification at `cost`, and one unit per signing request. -/
def gameCounted [DecidableEq Msg] [DecidableEq Sig] (mode : CountingMode)
    (cost : spec.Domain → ℕ) (scheme : SynchronizedSignature spec PK SK Msg Sig L)
    (adversary : Adversary spec PK Msg Sig L) : OracleComp spec (Bool × ℕ) := do
  let ((pk, sk), keygenCharged) ← charge (costIf mode.keygen cost) scheme.keygen
  let (((forgery, adversaryCharged), log) :
      (Forgery Msg Sig L × Multiplicative ℕ) × QueryLog (SigningSpec Msg Sig L)) ←
    (simulateQ
      ((QueryImpl.ofLift spec
          (WriterT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec))).withAddCost cost +
        signingOracleCounted (costIf mode.signer cost) (if mode.requests then 1 else 0) scheme sk)
      (adversary.main pk)).run.run
  let (verified, verifierCharged) ← charge (costIf mode.verifier cost)
    (scheme.verify pk forgery.epoch forgery.message forgery.signature)
  return (decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified,
    keygenCharged + Multiplicative.toAdd adversaryCharged + verifierCharged)

variable {Input Output : Type} [DecidableEq Input] [SampleableType Output]

/-- SUF-CMA in the random-oracle model for synchronized signature schemes, charging the hash calls
selected by `mode` (one unit per hash call, also for a repeated input; uniform samples are free)
and, if `mode.requests`, one unit per signing request. -/
noncomputable def notion [DecidableEq Msg] [DecidableEq Sig] (mode : CountingMode) :
    SecurityNotion
      (SynchronizedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L) where
  Adversary := Adversary (RandomOracleModel.World Input Output) PK Msg Sig L
  experiment := fun scheme adversary =>
    RandomOracleModel.run
      (gameCounted mode (RandomOracleModel.hashCost Input Output) scheme adversary)

end XmssSecurity.SUFCMA
