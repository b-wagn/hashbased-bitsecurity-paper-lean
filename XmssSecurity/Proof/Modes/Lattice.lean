import XmssSecurity.Statement.Security.SUFCMA

/-!
# Monotonicity of the counting modes

The sixteen notions `SUFCMA.notion mode` differ only in which queries of the experiment are
charged to the adversary. This file shows that the winning bit does not depend on the mode and
that the charge is monotone in the mode, so that a security proof for a mode transfers to every
mode charging more, and an attack transfers to every mode charging less.

The proof runs the experiment once with a vector-valued charge (`gameDetailed`), keeping the five
kinds of charged queries apart (`Kind`), and shows that `gameCounted mode` is its image under the
additive map `CountingMode.weight mode` summing the kinds selected by the mode.
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

namespace SUFCMA.CountingMode

/-- The pointwise order on counting modes: `m.Le m'` if every kind of query charged by `m` is
charged by `m'`. -/
def Le (m m' : CountingMode) : Prop :=
  (m.keygen → m'.keygen) ∧ (m.signer → m'.signer) ∧ (m.verifier → m'.verifier) ∧
    (m.requests → m'.requests)

end SUFCMA.CountingMode

namespace Modes

open SUFCMA

/-! ## Relabelling additive charges -/

section relabel

variable {ω ω' : Type} [AddMonoid ω] [AddMonoid ω']

/-- Apply an additive map to the charge component of the result of an `AddWriterT` run. -/
def relabel (f : ω →+ ω') {α : Type} (r : α × Multiplicative ω) : α × Multiplicative ω' :=
  (r.1, Multiplicative.ofAdd (f (Multiplicative.toAdd r.2)))

@[simp] lemma relabel_apply (f : ω →+ ω') {α : Type} (a : α) (w : Multiplicative ω) :
    relabel f (a, w) = (a, Multiplicative.ofAdd (f (Multiplicative.toAdd w))) := rfl

variable {M : Type → Type} [Monad M] [LawfulMonad M]

/-- Apply an additive map to the charge of an `AddWriterT` computation. -/
def relabelT (f : ω →+ ω') {α : Type} (x : AddWriterT ω M α) : AddWriterT ω' M α :=
  WriterT.mk (relabel f <$> x.run)

omit [LawfulMonad M] in
@[simp] lemma run_relabelT (f : ω →+ ω') {α : Type} (x : AddWriterT ω M α) :
    (relabelT f x).run = relabel f <$> x.run := rfl

lemma relabelT_pure (f : ω →+ ω') {α : Type} (a : α) :
    relabelT f (pure a : AddWriterT ω M α) = pure a := by
  apply WriterT.ext
  simp [relabelT, WriterT.run_pure]

lemma relabelT_bind (f : ω →+ ω') {α β : Type} (x : AddWriterT ω M α)
    (g : α → AddWriterT ω M β) :
    relabelT f (x >>= g) = relabelT f x >>= fun a => relabelT f (g a) := by
  apply WriterT.ext
  simp only [run_relabelT, WriterT.run_bind, map_bind, bind_map_left, Functor.map_map]
  refine bind_congr fun r => ?_
  refine map_congr fun s => ?_
  simp [relabel, toAdd_mul, ofAdd_add]

lemma relabelT_liftM (f : ω →+ ω') {P : Type → Type} [MonadLiftT P M] {α : Type} (y : P α) :
    relabelT f (liftM y : AddWriterT ω M α) = (liftM y : AddWriterT ω' M α) := by
  apply WriterT.ext
  change relabel f <$> ((fun a => (a, 1)) <$> (liftM y : M α)) = (fun a => (a, 1)) <$> (liftM y : M α)
  simp [Functor.map_map]

lemma relabelT_addTell (f : ω →+ ω') (w : ω) :
    relabelT f (AddWriterT.addTell (M := M) w) = AddWriterT.addTell (M := M) (f w) := by
  apply WriterT.ext
  simp [relabelT]

/-- Simulation commutes with relabelling: if two implementations agree up to relabelling the
charge on every query, so do their simulations. -/
lemma simulateQ_eq_relabelT {ι : Type} {spec : OracleSpec ι} (f : ω →+ ω')
    (impl : QueryImpl spec (AddWriterT ω M)) (impl' : QueryImpl spec (AddWriterT ω' M))
    (h : ∀ t, impl' t = relabelT f (impl t)) {α : Type} (x : OracleComp spec α) :
    simulateQ impl' x = relabelT f (simulateQ impl x) := by
  induction x using OracleComp.inductionOn with
  | pure a => simp [relabelT_pure]
  | query_bind t oa ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, h, ih, relabelT_bind]

/-- Charging by a relabelled cost is relabelling the charge. -/
lemma withAddCost_apply_eq_relabelT {ι : Type} {spec : OracleSpec ι} (f : ω →+ ω')
    (impl : QueryImpl spec M) {c : spec.Domain → ω} {c' : spec.Domain → ω'}
    (hc : ∀ t, f (c t) = c' t) (t : spec.Domain) :
    impl.withAddCost c' t = relabelT f (impl.withAddCost c t) := by
  rw [QueryImpl.withAddCost_apply, QueryImpl.withAddCost_apply, relabelT_bind, relabelT_addTell,
    hc]
  refine bind_congr fun _ => ?_
  exact (relabelT_liftM f _).symm

end relabel

/-! ## Charging with a vector-valued cost -/

section charge

variable {ι : Type} {spec : OracleSpec ι} {α : Type}

/-- As `SUFCMA.charge`, for a cost in any additive commutative monoid. -/
def chargeWith {ω : Type} [AddCommMonoid ω] (cost : spec.Domain → ω) (x : OracleComp spec α) :
    OracleComp spec (α × ω) :=
  (fun r => (r.1, Multiplicative.toAdd r.2)) <$> (simulateQ (addCostOracle cost) x).run

lemma charge_eq_chargeWith (cost : spec.Domain → ℕ) (x : OracleComp spec α) :
    charge cost x = chargeWith cost x := rfl

/-- Charging by a relabelled cost is relabelling the charge. -/
lemma chargeWith_eq_map {ω ω' : Type} [AddCommMonoid ω] [AddCommMonoid ω'] (f : ω →+ ω')
    {c : spec.Domain → ω} {c' : spec.Domain → ω'} (hc : ∀ t, f (c t) = c' t)
    (x : OracleComp spec α) :
    chargeWith c' x = (fun r => (r.1, f r.2)) <$> chargeWith c x := by
  unfold chargeWith addCostOracle
  rw [simulateQ_eq_relabelT f _ _ (withAddCost_apply_eq_relabelT f _ hc), run_relabelT]
  simp only [Functor.map_map]
  rfl

end charge

/-! ## The kinds of charged queries -/

/-- The kinds of queries that may be charged to the adversary. -/
inductive Kind
  /-- The adversary's own queries to the ambient oracles. -/
  | direct
  /-- The queries of key generation. -/
  | keygen
  /-- The queries of the signer. -/
  | signer
  /-- The queries of the final verification. -/
  | verifier
  /-- The signing requests. -/
  | requests
  deriving DecidableEq

/-- A charge per kind of query. -/
abbrev Charges := Kind → ℕ

namespace Kind

/-- The charge of `n` queries of kind `k`. -/
def single (k : Kind) (n : ℕ) : Charges := Pi.single k n

@[simp] lemma single_apply (k k' : Kind) (n : ℕ) :
    single k n k' = if k' = k then n else 0 := Pi.single_apply k n k'

end Kind

end Modes

namespace SUFCMA.CountingMode

open Modes

/-- The number of queries charged by `m` out of a charge per kind: the adversary's own queries,
and the kinds selected by `m`. -/
def weight (m : CountingMode) : Charges →+ ℕ where
  toFun c := c .direct + m.keygen.toNat * c .keygen + m.signer.toNat * c .signer +
    m.verifier.toNat * c .verifier + m.requests.toNat * c .requests
  map_zero' := by simp
  map_add' c c' := by simp only [Pi.add_apply]; ring

lemma weight_apply (m : CountingMode) (c : Charges) :
    m.weight c = c .direct + m.keygen.toNat * c .keygen + m.signer.toNat * c .signer +
      m.verifier.toNat * c .verifier + m.requests.toNat * c .requests := rfl

lemma toNat_le_toNat {b b' : Bool} (h : b → b') : b.toNat ≤ b'.toNat := by
  cases b <;> cases b' <;> simp_all

/-- `weight` is monotone in the mode. -/
lemma weight_le_weight {m m' : CountingMode} (h : m.Le m') (c : Charges) :
    m.weight c ≤ m'.weight c := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  simp only [weight_apply]
  gcongr
  · exact toNat_le_toNat h₁
  · exact toNat_le_toNat h₂
  · exact toNat_le_toNat h₃
  · exact toNat_le_toNat h₄

variable {ι : Type} {spec : OracleSpec ι}

lemma costIf_eq (b : Bool) (cost : spec.Domain → ℕ) (t : spec.Domain) :
    costIf b cost t = b.toNat * cost t := by
  cases b <;> simp [costIf]

lemma weight_single_direct (m : CountingMode) (cost : spec.Domain → ℕ) (t : spec.Domain) :
    m.weight (Kind.single .direct (cost t)) = cost t := by
  simp [weight_apply]

lemma weight_single_keygen (m : CountingMode) (cost : spec.Domain → ℕ) (t : spec.Domain) :
    m.weight (Kind.single .keygen (cost t)) = costIf m.keygen cost t := by
  simp [weight_apply, costIf_eq]

lemma weight_single_signer (m : CountingMode) (cost : spec.Domain → ℕ) (t : spec.Domain) :
    m.weight (Kind.single .signer (cost t)) = costIf m.signer cost t := by
  simp [weight_apply, costIf_eq]

lemma weight_single_verifier (m : CountingMode) (cost : spec.Domain → ℕ) (t : spec.Domain) :
    m.weight (Kind.single .verifier (cost t)) = costIf m.verifier cost t := by
  simp [weight_apply, costIf_eq]

lemma weight_single_requests (m : CountingMode) :
    m.weight (Kind.single .requests 1) = if m.requests then 1 else 0 := by
  cases h : m.requests <;> simp [weight_apply, h]

end SUFCMA.CountingMode

namespace Modes

open SUFCMA

/-! ## The experiment with a charge per kind -/

section game

variable {ι : Type} {spec : OracleSpec ι} {PK SK Msg Sig : Type} {L : ℕ}

/-- The monad of the adversary's run in `gameDetailed`: the charge per kind, the signing log, and
the ambient oracles. -/
abbrev DetailedRun (spec : OracleSpec ι) (Msg Sig : Type) (L : ℕ) : Type → Type :=
  AddWriterT Charges (WriterT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec))

/-- The signing oracle of `gameDetailed`: as `signingOracleCounted`, charging the signer's queries
at `cost` as kind `signer` and one unit of kind `requests` per request. -/
def signingOracleDetailed (cost : spec.Domain → ℕ)
    (scheme : SynchronizedSignature spec PK SK Msg Sig L) (sk : SK) :
    QueryImpl (SigningSpec Msg Sig L) (DetailedRun spec Msg Sig L) :=
  fun request => do
    let (answer, charged) ← liftM (chargeWith (fun t => Kind.single .signer (cost t))
      (scheme.sign sk request.epoch request.message))
    AddWriterT.addTell (M := WriterT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec))
      (Kind.single .requests 1 + charged)
    liftM (tell [⟨request, answer⟩] : WriterT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec) Unit)
    return answer

/-- The experiment as `gameCounted`, returning the charge per kind instead of its weighted sum. -/
def gameDetailed [DecidableEq Msg] [DecidableEq Sig] (cost : spec.Domain → ℕ)
    (scheme : SynchronizedSignature spec PK SK Msg Sig L)
    (adversary : Adversary spec PK Msg Sig L) : OracleComp spec (Bool × Charges) := do
  let ((pk, sk), keygenCharged) ← chargeWith (fun t => Kind.single .keygen (cost t)) scheme.keygen
  let (((forgery, adversaryCharged), log) :
      (Forgery Msg Sig L × Multiplicative Charges) × QueryLog (SigningSpec Msg Sig L)) ←
    (simulateQ
      ((QueryImpl.ofLift spec
          (WriterT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec))).withAddCost
            (fun t => Kind.single .direct (cost t)) +
        signingOracleDetailed cost scheme sk)
      (adversary.main pk)).run.run
  let (verified, verifierCharged) ← chargeWith (fun t => Kind.single .verifier (cost t))
    (scheme.verify pk forgery.epoch forgery.message forgery.signature)
  return (decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified,
    keygenCharged + Multiplicative.toAdd adversaryCharged + verifierCharged)

lemma run_run_liftM {γ : Type} (y : OracleComp spec γ) :
    (WriterT.run (liftM y : ChargedRun spec Msg Sig L γ)).run =
      (fun a => ((a, (1 : Multiplicative ℕ)), (∅ : QueryLog (SigningSpec Msg Sig L)))) <$> y := by
  change (fun r : γ × QueryLog (SigningSpec Msg Sig L) => ((r.1, (1 : Multiplicative ℕ)), r.2)) <$>
    ((fun a => (a, (∅ : QueryLog (SigningSpec Msg Sig L)))) <$> y) = _
  simp only [Functor.map_map]

/-- Lifting into the charged run commutes with `map`. -/
lemma liftM_map_chargedRun {α β : Type} (g : α → β) (x : OracleComp spec α) :
    (liftM (g <$> x) : ChargedRun spec Msg Sig L β) =
      g <$> (liftM x : ChargedRun spec Msg Sig L α) := by
  apply WriterT.ext
  apply WriterT.ext
  simp only [WriterT.run_map, run_run_liftM, Functor.map_map]

/-- The counted signing oracle of a mode is the detailed one with its charge weighted. -/
lemma signingOracleCounted_eq_relabelT (m : CountingMode) (cost : spec.Domain → ℕ)
    (scheme : SynchronizedSignature spec PK SK Msg Sig L) (sk : SK)
    (request : SignRequest Msg L) :
    signingOracleCounted (costIf m.signer cost) (if m.requests then 1 else 0) scheme sk request =
      relabelT m.weight (signingOracleDetailed cost scheme sk request) := by
  unfold signingOracleCounted signingOracleDetailed
  rw [relabelT_bind, relabelT_liftM, charge_eq_chargeWith,
    chargeWith_eq_map m.weight (m.weight_single_signer cost), liftM_map_chargedRun,
    bind_map_left]
  refine bind_congr fun r => ?_
  rcases r with ⟨answer, charged⟩
  dsimp only
  rw [relabelT_bind, relabelT_addTell, map_add, CountingMode.weight_single_requests]
  refine bind_congr fun _ => ?_
  rw [relabelT_bind, relabelT_liftM]
  refine bind_congr fun _ => ?_
  rw [relabelT_pure]

/-- The adversary's run of a mode is the detailed one with its charge weighted. -/
lemma simulateQ_counted_eq_relabelT (m : CountingMode) (cost : spec.Domain → ℕ)
    (scheme : SynchronizedSignature spec PK SK Msg Sig L) (sk : SK) {α : Type}
    (x : OracleComp (spec + SigningSpec Msg Sig L) α) :
    simulateQ
      ((QueryImpl.ofLift spec
          (WriterT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec))).withAddCost cost +
        signingOracleCounted (costIf m.signer cost) (if m.requests then 1 else 0) scheme sk) x =
      relabelT m.weight (simulateQ
        ((QueryImpl.ofLift spec
            (WriterT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec))).withAddCost
              (fun t => Kind.single .direct (cost t)) +
          signingOracleDetailed cost scheme sk) x) := by
  refine simulateQ_eq_relabelT m.weight _ _ (fun t => ?_) x
  rcases t with t | request
  · simp only [QueryImpl.add_apply_inl]
    exact withAddCost_apply_eq_relabelT m.weight _ (m.weight_single_direct cost) t
  · simp only [QueryImpl.add_apply_inr]
    exact signingOracleCounted_eq_relabelT m cost scheme sk request

/-- The counted experiment of a mode is the detailed one with its charge weighted. -/
theorem gameCounted_eq_map_gameDetailed [DecidableEq Msg] [DecidableEq Sig] (m : CountingMode)
    (cost : spec.Domain → ℕ) (scheme : SynchronizedSignature spec PK SK Msg Sig L)
    (adversary : Adversary spec PK Msg Sig L) :
    gameCounted m cost scheme adversary =
      (fun r => (r.1, m.weight r.2)) <$> gameDetailed cost scheme adversary := by
  unfold gameCounted gameDetailed
  rw [charge_eq_chargeWith, chargeWith_eq_map m.weight (m.weight_single_keygen cost)]
  simp only [map_bind, bind_map_left]
  refine bind_congr fun r => ?_
  rcases r with ⟨⟨pk, sk⟩, keygenCharged⟩
  dsimp only
  rw [simulateQ_counted_eq_relabelT m, run_relabelT, WriterT.run_map']
  simp only [bind_map_left]
  refine bind_congr fun r => ?_
  rcases r with ⟨⟨forgery, adversaryCharged⟩, log⟩
  dsimp only [Prod.map, relabel, id]
  rw [charge_eq_chargeWith, chargeWith_eq_map m.weight (m.weight_single_verifier cost)]
  simp only [bind_map_left]
  refine bind_congr fun r => ?_
  rcases r with ⟨verified, verifierCharged⟩
  simp only [map_pure, map_add, toAdd_ofAdd]
  rfl

end game

/-! ## Monotonicity in the mode -/

section monotone

variable {PK SK Msg Sig : Type} {L : ℕ} {Input Output : Type} [DecidableEq Input]
  [SampleableType Output] [DecidableEq Msg] [DecidableEq Sig]

/-- The experiment of `notion m` is the detailed experiment with its charge weighted by `m`. -/
lemma experiment_notion_eq (m : CountingMode)
    (scheme : SynchronizedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
    (adversary : Adversary (RandomOracleModel.World Input Output) PK Msg Sig L) :
    (notion m).experiment scheme adversary =
      (fun r => (r.1, m.weight r.2)) <$>
        RandomOracleModel.run (gameDetailed (RandomOracleModel.hashCost Input Output) scheme
          adversary) := by
  simp only [notion, RandomOracleModel.run, gameCounted_eq_map_gameDetailed, simulateQ_map,
    StateT.run'_map']

/-- The winning probability does not depend on the counting mode. -/
theorem advantage_eq_of_mode (m m' : CountingMode)
    (scheme : SynchronizedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
    (adversary : Adversary (RandomOracleModel.World Input Output) PK Msg Sig L) :
    (notion m).advantage scheme adversary = (notion m').advantage scheme adversary := by
  simp only [SecurityNotion.advantage, experiment_notion_eq, probEvent_map]
  rfl

/-- A query bound for a mode is a query bound for every mode charging less. -/
theorem hasQueryBound_of_le {m m' : CountingMode} (h : m.Le m')
    (scheme : SynchronizedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
    (adversary : Adversary (RandomOracleModel.World Input Output) PK Msg Sig L) (q : ℕ)
    (hq : (notion m').HasQueryBound scheme adversary q) :
    (notion m).HasQueryBound scheme adversary q := by
  intro r hr
  rw [experiment_notion_eq, support_map] at hr
  obtain ⟨s, hs, rfl⟩ := hr
  refine le_trans (CountingMode.weight_le_weight h s.2) ?_
  exact hq _ (by rw [experiment_notion_eq, support_map]; exact ⟨s, hs, rfl⟩)

/-- Security for a mode is security for every mode charging more. -/
theorem hasClassicalSecurityBits_of_le {m m' : CountingMode} (h : m.Le m')
    (scheme : SynchronizedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
    (bits : ℕ) (hs : (notion m).HasClassicalSecurityBits scheme bits) :
    (notion m').HasClassicalSecurityBits scheme bits := by
  intro q hq adversary hb
  rw [advantage_eq_of_mode m' m]
  exact hs q hq adversary (hasQueryBound_of_le h scheme adversary q hb)

/-- An attack on a mode is an attack on every mode charging less. -/
theorem not_hasClassicalSecurityBits_of_le {m m' : CountingMode} (h : m.Le m')
    (scheme : SynchronizedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
    (bits : ℕ) (hs : ¬ (notion m').HasClassicalSecurityBits scheme bits) :
    ¬ (notion m).HasClassicalSecurityBits scheme bits :=
  fun hm => hs (hasClassicalSecurityBits_of_le h scheme bits hm)

end monotone

end Modes

end XmssSecurity
