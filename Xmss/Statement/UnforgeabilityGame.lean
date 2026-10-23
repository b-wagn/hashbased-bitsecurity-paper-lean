import Xmss.Statement.EpochBasedSignature
import Xmss.Statement.RandomOracleModel
import Xmss.Statement.BitSecurity
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.QueryTracking.CostModel

/-!
# Unforgeability Games (Strong and Standard)
-/

open OracleComp OracleSpec ENNReal

namespace Xmss.Unforgeability

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

/-- A signing request returns a signature or `none`. -/
abbrev SigningSpec (Msg Sig : Type) (L : ℕ) : OracleSpec (SignRequest Msg L) :=
  SignRequest Msg L →ₒ Option Sig

/-! ## The signing transcript

The predicates a notion can use to say that a forgery is fresh. `Contains` gives SUF-CMA and
`ContainsRequest` gives EUF-CMA; both read the same table `Signed`. -/

namespace SigningTranscript

/-- Whether the table `Signed` has an entry at epoch `ep`, i.e. `Signed[ep] ≠ ⊥`. -/
def Signed (signed : QueryLog (SigningSpec Msg Sig L)) (epoch : Fin L) : Bool :=
  signed.any fun entry => decide (entry.1.epoch = epoch)

/-- The forgery's epoch/message/signature triple occurs in `Signed`. -/
def Contains [DecidableEq Msg] [DecidableEq Sig] (log : QueryLog (SigningSpec Msg Sig L))
    (forgery : Forgery Msg Sig L) : Prop :=
  ∃ entry ∈ log, entry.1 = forgery.request ∧ entry.2 = some forgery.signature

instance [DecidableEq Msg] [DecidableEq Sig] (log : QueryLog (SigningSpec Msg Sig L))
    (forgery : Forgery Msg Sig L) : Decidable (Contains log forgery) :=
  inferInstanceAs
    (Decidable (∃ entry ∈ log, entry.1 = forgery.request ∧ entry.2 = some forgery.signature))

/-- The forgery's epoch/message pair is in the table `Signed`, regardless of the answer. -/
def ContainsRequest (log : QueryLog (SigningSpec Msg Sig L)) (forgery : Forgery Msg Sig L) :
    Prop :=
  ∃ entry ∈ log, entry.1 = forgery.request

instance [DecidableEq Msg] (log : QueryLog (SigningSpec Msg Sig L))
    (forgery : Forgery Msg Sig L) : Decidable (ContainsRequest log forgery) :=
  inferInstanceAs (Decidable (∃ entry ∈ log, entry.1 = forgery.request))

end SigningTranscript

/-! ## Counting queries -/

/-- The kinds of queries counted by the experiment. -/
inductive QueryKind where
  /-- `q_S`: the adversary's signing queries. -/
  | sign
  /-- `q_H`: the hash queries the adversary makes directly. -/
  | hash
  /-- `q_Gen`: the hash queries of key generation. -/
  | keygen
  /-- `q_Sign`: the hash queries of the signer, summed over all signing queries. -/
  | signer
  /-- `q_Verify`: the hash queries of the verification of the forgery. -/
  | verifier
deriving DecidableEq, Fintype, Repr

/-- A count per kind of query. -/
abbrev QueryCounts := QueryKind → ℕ

/-- `n` queries of kind `kind`, and none of the other kinds. -/
def QueryCounts.single (kind : QueryKind) (n : ℕ) : QueryCounts := Pi.single kind n

variable {ι : Type} {spec : OracleSpec ι} {PK SK : Type}

/-- Run a computation, and also return the sum of `cost` over the queries it makes. -/
def countQueries {ω : Type} [AddCommMonoid ω] {α : Type} (cost : spec.Domain → ω)
    (computation : OracleComp spec α) : OracleComp spec (α × ω) :=
  (fun result => (result.1, Multiplicative.toAdd result.2)) <$>
    (simulateQ (addCostOracle cost) computation).run

/-! ## The experiment -/

/-- Given the public key and oracle access, return a claimed forgery. -/
structure Adversary {ι : Type} (spec : OracleSpec ι) (PK Msg Sig : Type) (L : ℕ) where
  main : PK → OracleComp (spec + SigningSpec Msg Sig L) (Forgery Msg Sig L)

/-- Query counts and the table `Signed`, over the ambient oracles. -/
abbrev CountedRun (spec : OracleSpec ι) (Msg Sig : Type) (L : ℕ) : Type → Type :=
  AddWriterT QueryCounts (StateT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec))

/-- Count the request; reject a used epoch, otherwise sign, count hashes, and record the answer. -/
def countedSigningOracle (cost : spec.Domain → ℕ)
    (scheme : EpochBasedSignature spec PK SK Msg Sig L) (sk : SK) :
    QueryImpl (SigningSpec Msg Sig L) (CountedRun spec Msg Sig L) :=
  fun request => do
    AddWriterT.addTell (QueryCounts.single .sign 1)
    let signed ← liftM (get : StateT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec) _)
    if SigningTranscript.Signed signed request.epoch then
      return none
    else
      let (answer, signerCounts) ← liftM (countQueries
        (fun t => QueryCounts.single .signer (cost t)) (scheme.sign sk request.epoch request.message))
      AddWriterT.addTell signerCounts
      liftM (set (signed ++ [⟨request, answer⟩]) :
        StateT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec) Unit)
      return answer

/-- Generate keys, run the adversary, and check freshness and verification; return win and counts. -/
def experiment (Fresh : QueryLog (SigningSpec Msg Sig L) → Forgery Msg Sig L → Prop)
    [∀ signed forgery, Decidable (Fresh signed forgery)] (cost : spec.Domain → ℕ)
    (scheme : EpochBasedSignature spec PK SK Msg Sig L)
    (adversary : Adversary spec PK Msg Sig L) : OracleComp spec (Bool × QueryCounts) := do
  let ((pk, sk), keygenCounts) ←
    countQueries (fun t => QueryCounts.single .keygen (cost t)) scheme.keygen
  let ((forgery, adversaryCounts), signed) ←
    (simulateQ
      ((QueryImpl.ofLift spec
          (StateT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec))).withAddCost
            (fun t => QueryCounts.single .hash (cost t)) +
        countedSigningOracle cost scheme sk)
      (adversary.main pk)).run.run []
  let (verified, verifierCounts) ← countQueries (fun t => QueryCounts.single .verifier (cost t))
    (scheme.verify pk forgery.epoch forgery.message forgery.signature)
  return (decide (Fresh signed forgery) && verified,
    keygenCounts + Multiplicative.toAdd adversaryCounts + verifierCounts)

variable {Input Output : Type} [DecidableEq Input] [SampleableType Output]

/-- Run the experiment with a shared random oracle and unit cost per hash call. -/
noncomputable def gameWith (Fresh : QueryLog (SigningSpec Msg Sig L) → Forgery Msg Sig L → Prop)
    [∀ signed forgery, Decidable (Fresh signed forgery)] :
    SecurityGame (EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
      QueryKind where
  Adversary := Adversary (RandomOracleModel.World Input Output) PK Msg Sig L
  experiment := fun scheme adversary =>
    RandomOracleModel.run
      (experiment Fresh (RandomOracleModel.hashCost Input Output) scheme adversary)

end Xmss.Unforgeability

namespace Xmss.SUFCMA

open Unforgeability

variable {PK SK Msg Sig : Type} {L : ℕ} {Input Output : Type} [DecidableEq Input]
  [SampleableType Output]

/-- SUF-CMA in the random-oracle model: a forgery is fresh if `(m*, σ*) ≠ Signed[ep*]`. -/
noncomputable abbrev securityGame [DecidableEq Msg] [DecidableEq Sig] :
    SecurityGame (EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
      QueryKind :=
  gameWith fun signed forgery => ¬SigningTranscript.Contains signed forgery

end Xmss.SUFCMA

namespace Xmss.EUFCMA

open Unforgeability

variable {PK SK Msg Sig : Type} {L : ℕ} {Input Output : Type} [DecidableEq Input]
  [SampleableType Output]

/-- EUF-CMA: the forgery's epoch/message pair must be absent from `Signed`. -/
noncomputable abbrev securityGame [DecidableEq Msg] :
    SecurityGame (EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
      QueryKind :=
  gameWith fun signed forgery => ¬SigningTranscript.ContainsRequest signed forgery

end Xmss.EUFCMA
