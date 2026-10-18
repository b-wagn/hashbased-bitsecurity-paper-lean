import XmssSecurity.Statement.Security.EUFCMA

/-!
# The games in which a repeated epoch loses

The proofs were written for a variant of the experiments of `Statement/Security/`: there the
signing oracle answers every request, also for an epoch already signed, and a transcript with two
requests for the same epoch makes the forgery lose (`SigningTranscript.Valid`). This file keeps
these experiments, as `lossyExperiment` and `lossyGame`, and `RepeatedEpochs.lean` transfers the
results to the experiments of the statement, in which a repeated epoch is answered by `⊥`.
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.SUFCMA

variable {Msg Sig : Type} {L : ℕ}

namespace SigningTranscript

/-- No epoch is requested twice. The adversary may request signatures adaptively, but a transcript
with two requests at the same epoch cannot win. -/
def Valid (log : QueryLog (SigningSpec Msg Sig L)) : Prop :=
  (log.map fun entry => entry.1.epoch).Nodup

instance (log : QueryLog (SigningSpec Msg Sig L)) : Decidable (Valid log) :=
  inferInstanceAs (Decidable ((log.map fun entry => entry.1.epoch).Nodup))

end SigningTranscript

variable {ι : Type} {spec : OracleSpec ι} {PK SK : Type}

/-- The adversary's run in the experiment: the counts so far, the signing log, and the ambient
oracles. -/
abbrev LossyRun (spec : OracleSpec ι) (Msg Sig : Type) (L : ℕ) : Type → Type :=
  AddWriterT QueryCounts (WriterT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec))

/-- The signing oracle `Sig(ep, m)` of the experiment: answer by `Sig(sk, ep, m)`, count one
signing query and the signer's hash queries (each at `cost`), and record the request and the
answer. -/
def lossySigningOracle (cost : spec.Domain → ℕ)
    (scheme : EpochBasedSignature spec PK SK Msg Sig L) (sk : SK) :
    QueryImpl (SigningSpec Msg Sig L) (LossyRun spec Msg Sig L) :=
  fun request => do
    let (answer, signerCounts) ← liftM (countQueries (fun t => QueryCounts.single .signer (cost t))
      (scheme.sign sk request.epoch request.message))
    AddWriterT.addTell (M := WriterT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec))
      (QueryCounts.single .sign 1 + signerCounts)
    liftM (tell [⟨request, answer⟩] : WriterT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec) Unit)
    return answer

/-- The lossy experiment for the freshness condition `Fresh`: key generation, the adversary with
the ambient oracles and the signing oracle, and verification of the forgery. The adversary wins
if the forgery verifies, the transcript is valid, and the forgery is fresh. -/
def lossyExperimentWith (Fresh : QueryLog (SigningSpec Msg Sig L) → Forgery Msg Sig L → Prop)
    [∀ log forgery, Decidable (Fresh log forgery)] (cost : spec.Domain → ℕ)
    (scheme : EpochBasedSignature spec PK SK Msg Sig L)
    (adversary : Adversary spec PK Msg Sig L) : OracleComp spec (Bool × QueryCounts) := do
  let ((pk, sk), keygenCounts) ←
    countQueries (fun t => QueryCounts.single .keygen (cost t)) scheme.keygen
  let (((forgery, adversaryCounts), log) :
      (Forgery Msg Sig L × Multiplicative QueryCounts) × QueryLog (SigningSpec Msg Sig L)) ←
    (simulateQ
      ((QueryImpl.ofLift spec
          (WriterT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec))).withAddCost
            (fun t => QueryCounts.single .hash (cost t)) +
        lossySigningOracle cost scheme sk)
      (adversary.main pk)).run.run
  let (verified, verifierCounts) ← countQueries (fun t => QueryCounts.single .verifier (cost t))
    (scheme.verify pk forgery.epoch forgery.message forgery.signature)
  return (decide (SigningTranscript.Valid log ∧ Fresh log forgery) && verified,
    keygenCounts + Multiplicative.toAdd adversaryCounts + verifierCounts)

/-- The lossy SUF-CMA experiment. -/
abbrev lossyExperiment [DecidableEq Msg] [DecidableEq Sig] (cost : spec.Domain → ℕ)
    (scheme : EpochBasedSignature spec PK SK Msg Sig L)
    (adversary : Adversary spec PK Msg Sig L) : OracleComp spec (Bool × QueryCounts) :=
  lossyExperimentWith (fun log forgery => ¬SigningTranscript.Contains log forgery) cost scheme
    adversary

variable {Input Output : Type} [DecidableEq Input] [SampleableType Output]

/-- The lossy experiment in the random-oracle model, counting as `SUFCMA.gameWith`. -/
noncomputable def lossyGameWith (Fresh : QueryLog (SigningSpec Msg Sig L) → Forgery Msg Sig L → Prop)
    [∀ log forgery, Decidable (Fresh log forgery)] :
    SecurityGame (EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
      QueryKind where
  Adversary := Adversary (RandomOracleModel.World Input Output) PK Msg Sig L
  experiment := fun scheme adversary =>
    RandomOracleModel.run
      (lossyExperimentWith Fresh (RandomOracleModel.hashCost Input Output) scheme adversary)

/-- The lossy SUF-CMA game. -/
noncomputable abbrev lossyGame [DecidableEq Msg] [DecidableEq Sig] :
    SecurityGame (EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
      QueryKind :=
  lossyGameWith fun log forgery => ¬SigningTranscript.Contains log forgery

end XmssSecurity.SUFCMA

namespace XmssSecurity.EUFCMA

open SUFCMA

variable {ι : Type} {spec : OracleSpec ι} {PK SK Msg Sig : Type} {L : ℕ}

/-- The lossy EUF-CMA experiment. -/
abbrev lossyExperiment [DecidableEq Msg] (cost : spec.Domain → ℕ)
    (scheme : EpochBasedSignature spec PK SK Msg Sig L)
    (adversary : Adversary spec PK Msg Sig L) : OracleComp spec (Bool × QueryCounts) :=
  lossyExperimentWith (fun log forgery => ¬SigningTranscript.ContainsRequest log forgery) cost
    scheme adversary

variable {Input Output : Type} [DecidableEq Input] [SampleableType Output]

/-- The lossy EUF-CMA game. -/
noncomputable abbrev lossyGame [DecidableEq Msg] :
    SecurityGame (EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
      QueryKind :=
  lossyGameWith fun log forgery => ¬SigningTranscript.ContainsRequest log forgery

end XmssSecurity.EUFCMA
