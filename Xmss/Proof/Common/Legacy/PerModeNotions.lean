import Xmss.Proof.Common.LossyGames

/-!
# The per-mode formulation of the security notions

The formulation of bit security and of SUF-CMA and EUF-CMA that the proofs were written against:
one `SecurityNotion` per counting mode, whose experiment returns the winning bit and the single
number of queries charged under that mode (`gameCounted`, `notion`). The statement layer instead
has one experiment per notion returning a count per kind of query
(`Unforgeability.lossyExperimentWith` of `LossyGames.lean`) and lets bit security sum the kinds
of a counting mode; `Proof/Common/Modes/QueryKinds.lean` proves the two formulations equivalent.
The EUF-CMA part is in `PerModeNotionsEUFCMA.lean`.

The definitions are kept verbatim, under their original names, so that the proofs are unchanged.
-/

open OracleComp OracleSpec ENNReal

namespace Xmss

/-- A security notion for schemes of type `Scheme`. -/
structure SecurityNotion (Scheme : Type) where
  /-- The adversaries of the notion. -/
  Adversary : Type
  /-- The experiment of an adversary against a scheme: whether it wins, and the number of
  queries charged to it. -/
  experiment : Scheme → Adversary → ProbComp (Bool × ℕ)

namespace SecurityNotion

variable {Scheme : Type} (notion : SecurityNotion Scheme) (scheme : Scheme)

/-- The probability that the adversary wins. -/
noncomputable def advantage (adversary : notion.Adversary) : ℝ≥0∞ :=
  Pr[fun result => result.1 = true | notion.experiment scheme adversary]

/-- Every execution of the experiment charges at most `q` queries. -/
def HasQueryBound (adversary : notion.Adversary) (q : ℕ) : Prop :=
  ∀ result ∈ support (notion.experiment scheme adversary), result.2 ≤ q

/-- Security at an arbitrary work factor. -/
def HasClassicalSecurityBound (workFactor : ℝ≥0∞) : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary, notion.HasQueryBound scheme adversary q →
    notion.advantage scheme adversary ≤ q / workFactor

/-- `bits` bits of classical security: every adversary with a query bound `q ≥ 1` wins with
probability at most `q / 2^bits`. -/
def HasClassicalSecurityBits (bits : ℕ) : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary, notion.HasQueryBound scheme adversary q →
    notion.advantage scheme adversary ≤ q / ((2 ^ bits : ℕ) : ℝ≥0∞)

/-- Exactly `bits` bits of classical security: `bits` bits (a security proof), but not
`bits + 1` bits (an attack). -/
def HasExactClassicalSecurityBits (bits : ℕ) : Prop :=
  notion.HasClassicalSecurityBits scheme bits ∧
    ¬ notion.HasClassicalSecurityBits scheme (bits + 1)

end SecurityNotion

end Xmss

namespace Xmss.Unforgeability

variable {Msg Sig : Type} {L : ℕ}

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

/-- The signing oracle: answer by the scheme's signer and record the request and answer. -/
def signingOracle (scheme : EpochBasedSignature spec PK SK Msg Sig L) (sk : SK) :
    QueryImpl (SigningSpec Msg Sig L)
      (WriterT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec)) :=
  QueryImpl.withLogging fun request => scheme.sign sk request.epoch request.message

/-- The monad of the adversary's run in `gameCounted`: the charged units, the signing log, and
the ambient oracles. -/
abbrev ChargedRun (spec : OracleSpec ι) (Msg Sig : Type) (L : ℕ) : Type → Type :=
  AddWriterT ℕ (WriterT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec))

/-- The signing oracle of `gameCounted`: as `signingOracle`, additionally charging the signer's
queries by `signerCost` and `requestCost` units per request. -/
def signingOracleCounted (signerCost : spec.Domain → ℕ) (requestCost : ℕ)
    (scheme : EpochBasedSignature spec PK SK Msg Sig L) (sk : SK) :
    QueryImpl (SigningSpec Msg Sig L) (ChargedRun spec Msg Sig L) :=
  fun request => do
    let (answer, charged) ← liftM (charge signerCost (scheme.sign sk request.epoch request.message))
    AddWriterT.addTell (M := WriterT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec))
      (requestCost + charged)
    liftM (tell [⟨request, answer⟩] : WriterT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec) Unit)
    return answer

end Xmss.Unforgeability

namespace Xmss.SUFCMA

open Unforgeability

variable {ι : Type} {spec : OracleSpec ι} {PK SK Msg Sig : Type} {L : ℕ}

/-- The experiment, before any accounting: key generation, the adversary with the ambient oracles
forwarded and the logged signing oracle, and verification of the forgery. The notions are stated
with `gameCounted`, which adds the accounting; `Proof/Common/Modes/` shows that `gameCounted`
projects to `game` in every mode. -/
def game [DecidableEq Msg] [DecidableEq Sig]
    (scheme : EpochBasedSignature spec PK SK Msg Sig L)
    (adversary : Adversary spec PK Msg Sig L) : OracleComp spec Bool := do
  let (pk, sk) ← scheme.keygen
  let ((forgery, log) : Forgery Msg Sig L × QueryLog (SigningSpec Msg Sig L)) ←
    (simulateQ
      (QueryImpl.ofLift spec (WriterT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec)) +
        signingOracle scheme sk)
      (adversary.main pk)).run
  let verified ← scheme.verify pk forgery.epoch forgery.message forgery.signature
  return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified

/-- The experiment as `game`, additionally returning the number of queries charged to the
adversary under `mode`: its own queries to the ambient oracles at `cost`, and, as the mode says,
the queries of key generation at `cost`, the queries of the signer at `cost`, the queries of the
final verification at `cost`, and one unit per signing request. -/
def gameCounted [DecidableEq Msg] [DecidableEq Sig] (mode : CountingMode)
    (cost : spec.Domain → ℕ) (scheme : EpochBasedSignature spec PK SK Msg Sig L)
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

/-- SUF-CMA in the random-oracle model for epoch-based signature schemes, charging the hash calls
selected by `mode` (one unit per hash call, also for a repeated input; uniform samples are free)
and, if `mode.requests`, one unit per signing request. -/
noncomputable def notion [DecidableEq Msg] [DecidableEq Sig] (mode : CountingMode) :
    SecurityNotion
      (EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L) where
  Adversary := Adversary (RandomOracleModel.World Input Output) PK Msg Sig L
  experiment := fun scheme adversary =>
    RandomOracleModel.run
      (gameCounted mode (RandomOracleModel.hashCost Input Output) scheme adversary)

end Xmss.SUFCMA
