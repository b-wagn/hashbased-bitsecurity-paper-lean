import XmssSecurity.Statement.Security.SUFCMA

/-!
# Correctness

The experiment `CORRECT_SIG(A)` of the definition of correctness of the manuscript, for an
epoch-based signature scheme `SIG = (Gen, Sig, Ver)` in the random-oracle model and an adversary
`A`:

1. generate keys `(pk, sk) ← Gen` and set `v := 0`;
2. run `A` on `pk`, with access to the hash oracle, private uniform sampling, and the signing
   oracle `Sig(ep, m)`: if `Signed[ep] ≠ ⊥`, it returns `⊥`; otherwise it computes
   `σ ← Sig(sk, ep, m)` and sets `Signed[ep] := (m, σ)`; if `σ = ⊥` or `Ver(pk, ep, m, σ) = 0`, it
   sets `v := 1`; it returns `σ`;
3. output `v`.

The experiment also outputs the number of signing queries of `A`. The correctness advantage is
`Pr[CORRECT_SIG(A) = 1]`, and `SIG` has correctness error at most `δ` if this advantage is at
most `δ · q` for every adversary that makes at most `q` signing queries. The adversary's hash
queries are not limited.
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Correctness

open SUFCMA

variable {ι : Type} {spec : OracleSpec ι} {PK SK Msg Sig : Type} {L : ℕ}

/-- An adaptive adversary of the correctness experiment: given the public key, it may use the
ambient oracles and the signing oracle. -/
structure Adversary {ι : Type} (spec : OracleSpec ι) (PK Msg Sig : Type) (L : ℕ) where
  main : PK → OracleComp (spec + SigningSpec Msg Sig L) Unit

/-- The adversary's run in the experiment: the number of signing queries, the table `Signed` and
the flag `v`, and the ambient oracles. -/
abbrev Run (spec : OracleSpec ι) (Msg Sig : Type) (L : ℕ) : Type → Type :=
  AddWriterT ℕ (StateT (QueryLog (SigningSpec Msg Sig L) × Bool) (OracleComp spec))

/-- The signing oracle `Sig(ep, m)` of the experiment. It counts one signing query. If
`Signed[ep] ≠ ⊥`, it returns `⊥`. Otherwise it signs, records the request and the answer as
`Signed[ep]`, and sets the flag `v` if the answer is `⊥` or does not verify. -/
def signingOracle (scheme : EpochBasedSignature spec PK SK Msg Sig L) (pk : PK) (sk : SK) :
    QueryImpl (SigningSpec Msg Sig L) (Run spec Msg Sig L) :=
  fun request => do
    AddWriterT.addTell (M := StateT (QueryLog (SigningSpec Msg Sig L) × Bool) (OracleComp spec)) 1
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

/-- The experiment `CORRECT_SIG(A)`: key generation, and the adversary with the ambient oracles
and the signing oracle, starting from the empty table `Signed` and `v = 0`. It returns `v` and
the number of signing queries. -/
def experiment (scheme : EpochBasedSignature spec PK SK Msg Sig L)
    (adversary : Adversary spec PK Msg Sig L) : OracleComp spec (Bool × ℕ) := do
  let (pk, sk) ← scheme.keygen
  let ((_, requests), (_, failed)) ←
    ((simulateQ (QueryImpl.ofLift spec (Run spec Msg Sig L) + signingOracle scheme pk sk)
      (adversary.main pk)).run.run ([], false))
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

/-- Correctness error at most `δ`: every adversary that makes at most `q` signing queries makes
signing fail, or a signature not verify, with probability at most `δ · q`. -/
def HasCorrectnessError
    (scheme : EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
    (δ : ℝ≥0∞) : Prop :=
  ∀ q adversary, HasRequestBound scheme adversary q → advantage scheme adversary ≤ δ * q

end XmssSecurity.Correctness
