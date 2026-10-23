import Xmss.Proof.Common.Adversary.LegacyNotions

/-!
# Charging queries commutes with simulation

Charging the queries of a program and then simulating it with `impl` is simulating it with the
charging implementation `impl.withAddCost cost` (`simulateQ_run_simulateQ_addCostOracle`), also
under a log writer layer (`simulateQ_run_run_simulateQ`). The lemmas are generic in the oracle
implementation and in the cost, and they move the accounting of `gameCounted` out of the
simulation, stage by stage, up to the adversary's own run (`simulateQ_adversaryRun`).
-/

open OracleComp OracleSpec ENNReal

namespace Xmss.Modes

section lifts

/-- `liftM` into a writer over a lifted monad, run. -/
theorem run_liftM_of_liftM {m n : Type → Type} [Monad m] [MonadLiftT n m] {ω' : Type} [Monoid ω']
    {α : Type} (x : n α) :
    (liftM x : WriterT ω' m α).run = (fun a => (a, 1)) <$> (liftM x : m α) := rfl

/-- `liftM` into a log writer over a lifted monad, run. -/
theorem run_liftM_of_liftM' {m n : Type → Type} [Monad m] [MonadLiftT n m] {L : Type}
    [EmptyCollection L] {α : Type} (x : n α) :
    (liftM x : WriterT L m α).run = (fun a => (a, ∅)) <$> (liftM x : m α) := rfl

end lifts

section generic

variable {ι : Type} {spec : OracleSpec ι} {m : Type → Type} [Monad m] [LawfulMonad m]
  {ω : Type} [AddCommMonoid ω]

/-- Simulating a cost-charged program with `impl` is simulating it with the charging
implementation `impl.withAddCost cost`. -/
theorem simulateQ_run_simulateQ_addCostOracle (impl : QueryImpl spec m)
    (cost : spec.Domain → ω) {α : Type} (x : OracleComp spec α) :
    simulateQ impl (simulateQ (addCostOracle cost) x).run =
      (simulateQ (impl.withAddCost cost) x).run := by
  induction x using OracleComp.inductionOn with
  | pure a => simp [WriterT.run_pure]
  | query_bind t k ih =>
    simp only [addCostOracle, QueryImpl.ofLift_eq_id'] at ih
    simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind, simulateQ_map]
    simp only [addCostOracle, QueryImpl.withAddCost_apply, WriterT.run_bind, WriterT.run_monadLift,
      AddWriterT.run_addTell, pure_bind, Functor.map_map, simulateQ_map,
      simulateQ_spec_query, QueryImpl.ofLift_eq_id', QueryImpl.id'_apply, ih]

/-- Simulating a charged program with `impl` is simulating it with the charging implementation
and converting the cost. -/
theorem simulateQ_charge (impl : QueryImpl spec m) (cost : spec.Domain → ℕ) {α : Type}
    (x : OracleComp spec α) :
    simulateQ impl (Unforgeability.charge cost x) =
      (fun r => (r.1, Multiplicative.toAdd r.2)) <$> (simulateQ (impl.withAddCost cost) x).run := by
  rw [Unforgeability.charge, simulateQ_map, simulateQ_run_simulateQ_addCostOracle]

/-- Exchange the two layers of a doubly written result. -/
abbrev swapLayers {α L ω' : Type} (r : (α × L) × ω') : (α × ω') × L := ((r.1.1, r.2), r.1.2)

/-- Simulating a program written to a cost layer over a log layer with `impl₁` equals simulating
the program written to the log layer only with a cost-tracking `impl₂`, as soon as this holds
query by query. -/
theorem simulateQ_run_run_simulateQ {ι' : Type} {spec' : OracleSpec ι'}
    {L : Type} [EmptyCollection L] [Append L] [LawfulAppend L] {ω' : Type} [Monoid ω']
    (impl₁ : QueryImpl spec m) (impl₂ : QueryImpl spec (WriterT ω' m))
    (implC : QueryImpl spec' (WriterT ω' (WriterT L (OracleComp spec))))
    (implG : QueryImpl spec' (WriterT L (OracleComp spec)))
    (h : ∀ t, simulateQ impl₁ (implC t).run.run =
      swapLayers <$> (simulateQ impl₂ (implG t).run).run)
    {α : Type} (x : OracleComp spec' α) :
    simulateQ impl₁ (simulateQ implC x).run.run =
      swapLayers <$> (simulateQ impl₂ (simulateQ implG x).run).run := by
  induction x using OracleComp.inductionOn with
  | pure a => simp [WriterT.run_pure]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind, WriterT.run_map',
      simulateQ_map, Functor.map_map, map_bind, bind_map_left, h, ih]
    simp [Prod.map]

end generic

section sufcma

variable {ι : Type} {spec : OracleSpec ι} {m : Type → Type} [Monad m] [LawfulMonad m]
  {PK SK Msg Sig : Type} {L : ℕ}

/-- The log writer of the adversary's run. -/
local notation "LogW" => WriterT (QueryLog (Unforgeability.SigningSpec Msg Sig L)) (OracleComp spec)

/-- The charged forwarding oracle, query by query. -/
theorem simulateQ_withAddCost_ofLift_apply (impl : QueryImpl spec m) (cost : spec.Domain → ℕ)
    (s : spec.Domain) :
    simulateQ impl ((QueryImpl.ofLift spec LogW).withAddCost cost s).run.run =
      swapLayers <$>
        (simulateQ (impl.withAddCost cost) (QueryImpl.ofLift spec LogW s).run).run := by
  simp only [QueryImpl.withAddCost_apply, QueryImpl.ofLift_apply, WriterT.run_bind,
    WriterT.run_map, AddWriterT.run_addTell, WriterT.run_monadLift, run_liftM_of_liftM',
    pure_bind, Functor.map_map, map_bind, simulateQ_map, simulateQ_spec_query, mul_one,
    swapLayers]

/-- The charged signing oracle, query by query. -/
theorem simulateQ_signingOracleCounted_apply (impl : QueryImpl spec m) (cost : spec.Domain → ℕ)
    (scheme : EpochBasedSignature spec PK SK Msg Sig L) (sk : SK)
    (r : Unforgeability.SignRequest Msg L) :
    simulateQ impl (Unforgeability.signingOracleCounted cost 0 scheme sk r).run.run =
      swapLayers <$>
        (simulateQ (impl.withAddCost cost) (Unforgeability.signingOracle scheme sk r).run).run := by
  simp only [QueryImpl.withLogging_apply, Unforgeability.signingOracleCounted, Unforgeability.signingOracle,
    WriterT.run_bind, WriterT.run_pure, WriterT.run_tell, AddWriterT.run_addTell,
    WriterT.run_monadLift, WriterT.run_monadLift', run_liftM_of_liftM, pure_bind, map_pure,
    map_bind, bind_map_left, simulateQ_bind, simulateQ_pure, simulateQ_charge, zero_add, mul_one,
    one_mul, LawfulAppend.empty_append, LawfulAppend.append_empty, ofAdd_toAdd, swapLayers]

/-- Query by query, the charged oracles of `gameCounted` simulated with `impl` are the
oracles of `game` simulated with the charging implementation. -/
theorem simulateQ_countedOracles_apply (impl : QueryImpl spec m) (cost : spec.Domain → ℕ)
    (scheme : EpochBasedSignature spec PK SK Msg Sig L) (sk : SK)
    (t : (spec + Unforgeability.SigningSpec Msg Sig L).Domain) :
    simulateQ impl
      (((QueryImpl.ofLift spec LogW).withAddCost cost +
        Unforgeability.signingOracleCounted cost 0 scheme sk) t).run.run =
      swapLayers <$> (simulateQ (impl.withAddCost cost)
        ((QueryImpl.ofLift spec LogW + Unforgeability.signingOracle scheme sk) t).run).run := by
  rcases t with s | r
  · exact simulateQ_withAddCost_ofLift_apply impl cost s
  · exact simulateQ_signingOracleCounted_apply impl cost scheme sk r

/-- The adversary's run of `gameCounted` simulated with `impl` is its run of `game`
simulated with the charging implementation. -/
theorem simulateQ_adversaryRun (impl : QueryImpl spec m) (cost : spec.Domain → ℕ)
    (scheme : EpochBasedSignature spec PK SK Msg Sig L) (sk : SK)
    (adversary : Unforgeability.Adversary spec PK Msg Sig L) (pk : PK) :
    simulateQ impl
      (simulateQ ((QueryImpl.ofLift spec LogW).withAddCost cost +
        Unforgeability.signingOracleCounted cost 0 scheme sk) (adversary.main pk)).run.run =
      swapLayers <$> (simulateQ (impl.withAddCost cost)
        (simulateQ (QueryImpl.ofLift spec LogW + Unforgeability.signingOracle scheme sk)
          (adversary.main pk)).run).run :=
  simulateQ_run_run_simulateQ impl (impl.withAddCost cost) _ _
    (simulateQ_countedOracles_apply impl cost scheme sk) (adversary.main pk)

end sufcma

end Xmss.Modes
