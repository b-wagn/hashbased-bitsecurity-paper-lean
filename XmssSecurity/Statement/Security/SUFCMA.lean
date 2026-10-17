import XmssSecurity.Statement.EpochBasedSignature
import XmssSecurity.Statement.RandomOracleModel
import XmssSecurity.Statement.BitSecurity
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.QueryTracking.CostModel

/-!
# Strong unforgeability under chosen-message attacks

The experiment `SUFCMA_SIG(A)` of the definition of unforgeability of the manuscript, for an
epoch-based signature scheme `SIG = (Gen, Sig, Ver)` in the random-oracle model and an adversary `A`:

1. generate keys `(pk, sk) ← Gen`;
2. run `A` on `pk`, with access to the hash oracle, private uniform sampling, and the signing
   oracle `Sig(ep, m)`: if `Signed[ep] ≠ ⊥`, it returns `⊥`; otherwise it computes
   `σ ← Sig(sk, ep, m)` (a signature, or `⊥` if the signer fails), sets `Signed[ep] := (m, σ)`,
   and returns `σ`;
3. obtain from `A` a forgery `(ep*, m*, σ*)`;
4. determine winning: `v = 1` if `Ver(pk, ep*, m*, σ*) = 1` and `(m*, σ*) ≠ Signed[ep*]`;
   otherwise `v = 0`;
5. count queries, one count per `QueryKind`: the signing queries of `A` (`q_S`), the hash queries
   `A` made directly (`q_H`), and the hash queries of key generation (`q_Gen`), of the signer
   summed over all signing queries (`q_Sig`), and of the verification in step 4 (`q_Ver`);
6. output `v` and the counts.

The honest signer never signs twice for the same epoch: a second request for an epoch is answered
by `⊥` without running the signer. It still counts as a signing query, and the signer makes no hash
query for it. The table `Signed` is the list of the answered requests, in order. The adversary has
no verification oracle; the only verification is the experiment's final check. Every hash call
counts one unit, also for a repeated input; uniform sampling is free.

`securityGame` is this experiment in the random-oracle model, as a `SecurityGame`
(`BitSecurity.lean`); a counting mode then selects which of the counts form the adversary's work.
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

/-- The signer answered the forgery's request with the forgery's signature:
`(m*, σ*) = Signed[ep*]`. A different signature for a requested epoch and message is therefore a
valid strong forgery. -/
def Contains [DecidableEq Msg] [DecidableEq Sig] (log : QueryLog (SigningSpec Msg Sig L))
    (forgery : Forgery Msg Sig L) : Prop :=
  ∃ entry ∈ log, entry.1 = forgery.request ∧ entry.2 = some forgery.signature

instance [DecidableEq Msg] [DecidableEq Sig] (log : QueryLog (SigningSpec Msg Sig L))
    (forgery : Forgery Msg Sig L) : Decidable (Contains log forgery) :=
  inferInstanceAs
    (Decidable (∃ entry ∈ log, entry.1 = forgery.request ∧ entry.2 = some forgery.signature))

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
  /-- `q_Sig`: the hash queries of the signer, summed over all signing queries. -/
  | signer
  /-- `q_Ver`: the hash queries of the verification of the forgery. -/
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

/-- An adaptive adversary: given the public key, it may use the ambient oracles and the signing
oracle, and returns a claimed forgery. -/
structure Adversary {ι : Type} (spec : OracleSpec ι) (PK Msg Sig : Type) (L : ℕ) where
  main : PK → OracleComp (spec + SigningSpec Msg Sig L) (Forgery Msg Sig L)

/-- The adversary's run in the experiment: the counts so far, the table `Signed` of answered
requests, and the ambient oracles. -/
abbrev CountedRun (spec : OracleSpec ι) (Msg Sig : Type) (L : ℕ) : Type → Type :=
  AddWriterT QueryCounts (StateT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec))

/-- Whether the table `Signed` has an entry at epoch `ep`, i.e. `Signed[ep] ≠ ⊥`. -/
def SigningTranscript.Signed (signed : QueryLog (SigningSpec Msg Sig L)) (epoch : Fin L) : Bool :=
  signed.any fun entry => decide (entry.1.epoch = epoch)

/-- The signing oracle `Sig(ep, m)` of the experiment. It counts one signing query. If
`Signed[ep] ≠ ⊥`, it returns `⊥`. Otherwise it answers by `Sig(sk, ep, m)`, counts the signer's
hash queries (each at `cost`), and records the request and the answer as `Signed[ep]`. -/
def countedSigningOracle (cost : spec.Domain → ℕ)
    (scheme : EpochBasedSignature spec PK SK Msg Sig L) (sk : SK) :
    QueryImpl (SigningSpec Msg Sig L) (CountedRun spec Msg Sig L) :=
  fun request => do
    AddWriterT.addTell (M := StateT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec))
      (QueryCounts.single .sign 1)
    let signed ← liftM (get : StateT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec) _)
    if SigningTranscript.Signed signed request.epoch then
      return none
    else
      let (answer, signerCounts) ← liftM (countQueries
        (fun t => QueryCounts.single .signer (cost t)) (scheme.sign sk request.epoch request.message))
      AddWriterT.addTell (M := StateT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec))
        signerCounts
      liftM (set (signed ++ [⟨request, answer⟩]) :
        StateT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec) Unit)
      return answer

/-- The experiment `SUFCMA_SIG(A)`: key generation, the adversary with the ambient oracles and the
signing oracle, starting from the empty table `Signed`, and verification of the forgery. It
returns the winning bit `v` and the count of each kind of query, where every query of the ambient
oracles counts `cost` (in the random-oracle model: one per hash call, none per uniform sample). -/
def experiment [DecidableEq Msg] [DecidableEq Sig] (cost : spec.Domain → ℕ)
    (scheme : EpochBasedSignature spec PK SK Msg Sig L)
    (adversary : Adversary spec PK Msg Sig L) : OracleComp spec (Bool × QueryCounts) := do
  let ((pk, sk), keygenCounts) ←
    countQueries (fun t => QueryCounts.single .keygen (cost t)) scheme.keygen
  let (((forgery, adversaryCounts), signed) :
      (Forgery Msg Sig L × Multiplicative QueryCounts) × QueryLog (SigningSpec Msg Sig L)) ←
    ((simulateQ
      ((QueryImpl.ofLift spec
          (StateT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec))).withAddCost
            (fun t => QueryCounts.single .hash (cost t)) +
        countedSigningOracle cost scheme sk)
      (adversary.main pk)).run.run [])
  let (verified, verifierCounts) ← countQueries (fun t => QueryCounts.single .verifier (cost t))
    (scheme.verify pk forgery.epoch forgery.message forgery.signature)
  return (decide (¬SigningTranscript.Contains signed forgery) && verified,
    keygenCounts + Multiplicative.toAdd adversaryCounts + verifierCounts)

variable {Input Output : Type} [DecidableEq Input] [SampleableType Output]

/-- SUF-CMA in the random-oracle model: the experiment with the lazily sampled random oracle,
counting one unit per hash call (also for a repeated input) and nothing per uniform sample. -/
noncomputable def securityGame [DecidableEq Msg] [DecidableEq Sig] :
    SecurityGame (EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
      QueryKind where
  Adversary := Adversary (RandomOracleModel.World Input Output) PK Msg Sig L
  experiment := fun scheme adversary =>
    RandomOracleModel.run
      (SUFCMA.experiment (RandomOracleModel.hashCost Input Output) scheme adversary)

end XmssSecurity.SUFCMA
