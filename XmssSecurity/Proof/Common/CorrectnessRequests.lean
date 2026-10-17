import XmssSecurity.Statement.Security.Correctness
import XmssSecurity.Proof.Common.RepeatedEpochs

/-!
# The flag of the correctness experiment needs a signing query

Only the signing oracle sets the flag `v` of the correctness experiment, and it counts the query
first. So every run that outputs `v = 1` made a signing query (`experiment_flag_requests`), and an
adversary without signing queries has correctness advantage `0`.
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Correctness

open SUFCMA

variable {ι : Type} {spec : OracleSpec ι} {PK SK Msg Sig : Type} {L : ℕ}

theorem run_query_bind (scheme : EpochBasedSignature spec PK SK Msg Sig L) (pk : PK) (sk : SK)
    {α : Type} (input : (spec + SigningSpec Msg Sig L).Domain)
    (next : (spec + SigningSpec Msg Sig L).Range input →
      OracleComp (spec + SigningSpec Msg Sig L) α)
    (state : QueryLog (SigningSpec Msg Sig L) × Bool) :
    (simulateQ (QueryImpl.ofLift spec (Run spec Msg Sig L) + signingOracle scheme pk sk)
        (liftM ((spec + SigningSpec Msg Sig L).query input) >>= next)).run.run state =
      ((QueryImpl.ofLift spec (Run spec Msg Sig L) + signingOracle scheme pk sk) input).run.run
          state >>= fun p =>
        (fun q => ((q.1.1, p.1.2 * q.1.2), q.2)) <$>
          (simulateQ (QueryImpl.ofLift spec (Run spec Msg Sig L) + signingOracle scheme pk sk)
            (next p.1.1)).run.run p.2 := by
  simp [simulateQ_bind, WriterT.run_bind, StateT.run_bind]

theorem run_flag_requests (scheme : EpochBasedSignature spec PK SK Msg Sig L) (pk : PK) (sk : SK)
    {α : Type} (computation : OracleComp (spec + SigningSpec Msg Sig L) α) :
    ∀ (state : QueryLog (SigningSpec Msg Sig L) × Bool),
      ∀ result ∈ support ((simulateQ (QueryImpl.ofLift spec (Run spec Msg Sig L) +
          signingOracle scheme pk sk) computation).run.run state),
        result.2.2 = true → state.2 = true ∨ 1 ≤ Multiplicative.toAdd result.1.2 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro state result hresult hflag
      simp only [simulateQ_pure, WriterT.run_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hresult
      subst hresult
      exact Or.inl hflag
  | query_bind input next ih =>
      intro state result hresult hflag
      rw [run_query_bind] at hresult
      obtain ⟨step, hstep, hrest⟩ := (mem_support_bind_iff _ _ _).1 hresult
      rw [support_map] at hrest
      obtain ⟨inner, hinner, rfl⟩ := hrest
      rcases input with t | request
      · have hstate : step.2 = state ∧ step.1.2 = 1 := by
          change step ∈ support (((liftM (spec.query t) : Run spec Msg Sig L _)).run.run state)
            at hstep
          rw [writerState_run_lift, support_map] at hstep
          obtain ⟨answer, -, rfl⟩ := hstep
          exact ⟨rfl, rfl⟩
        rcases ih step.1.1 step.2 inner hinner hflag with hleft | hright
        · rw [hstate.1] at hleft
          exact Or.inl hleft
        · refine Or.inr ?_
          simp only [toAdd_mul, hstate.2, toAdd_one, zero_add]
          exact hright
      · have hcount : 1 ≤ Multiplicative.toAdd step.1.2 := by
          change step ∈ support ((signingOracle scheme pk sk request).run.run state) at hstep
          unfold signingOracle at hstep
          simp only [WriterT.run_bind, StateT.run_bind, AddWriterT.run_addTell, pure_bind,
            StateT.run_map, support_map] at hstep
          obtain ⟨rest, -, rfl⟩ := hstep
          simp
        refine Or.inr ?_
        simp only [toAdd_mul]
        omega

/-- A run of the correctness experiment that outputs `v = 1` made a signing query. -/
theorem experiment_flag_requests (scheme : EpochBasedSignature spec PK SK Msg Sig L)
    (adversary : Adversary spec PK Msg Sig L) :
    ∀ result ∈ support (experiment scheme adversary), result.1 = true → 1 ≤ result.2 := by
  intro result hresult hflag
  unfold experiment at hresult
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hresult
  obtain ⟨keys, -, run, hrun, rfl⟩ := hresult
  rcases run_flag_requests scheme keys.1 keys.2 (adversary.main keys.1) ([], false) run hrun
    hflag with hfalse | hcount
  · simp at hfalse
  · exact hcount

variable {Input Output : Type} [DecidableEq Input] [SampleableType Output]

/-- An adversary without signing queries has correctness advantage `0`. -/
theorem advantage_eq_zero_of_noRequests
    (scheme : EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
    (adversary : Adversary (RandomOracleModel.World Input Output) PK Msg Sig L)
    (hbound : HasRequestBound scheme adversary 0) : advantage scheme adversary = 0 := by
  unfold advantage
  rw [probEvent_eq_zero_iff]
  intro result hresult hflag
  have hzero := (probEvent_eq_one_iff.1 hbound).2 result hresult
  have hsub := support_simulateQ_run'_subset _ _ _ hresult
  have := experiment_flag_requests scheme adversary result hsub hflag
  omega

end XmssSecurity.Correctness
