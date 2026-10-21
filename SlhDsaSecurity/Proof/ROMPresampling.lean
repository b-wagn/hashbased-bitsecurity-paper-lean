import SlhDsaSecurity.Statement.Security
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling

/-!
# Unobserved preparation in the actual shared byte random oracle

Arbitrary finite adaptive oracle work may be performed before a computation when
its returned value is discarded. The output distribution is unchanged, including
any query counters already instrumented inside the continuation. This is the
presampling step needed to materialize a canonical graph for the security proof.
The final cache itself is deliberately not claimed to have the same distribution.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.ROMPresampling

set_option backward.isDefEq.respectTransparency false

noncomputable abbrev romImpl := XmssSecurity.RandomOracleModel.impl Bytes HashOutput

theorem run'_query_bind {α : Type} (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) :
    (simulateQ romImpl (liftM (OracleWorld.query input) >>= next)).run' cache =
      ((romImpl input).run cache >>= fun result =>
        (simulateQ romImpl (next result.1)).run' result.2) := by
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, map_bind]

theorem cacheQuery_comm (cache : QueryCache HashSpec) (left right : Bytes)
    (h : left ≠ right) (a b : HashOutput) :
    (cache.cacheQuery left a).cacheQuery right b = (cache.cacheQuery right b).cacheQuery left a := by
  funext input
  by_cases hl : input = left
  · subst input
    simp [QueryCache.cacheQuery_of_ne, h]
  · by_cases hr : input = right
    · subst input
      simp [QueryCache.cacheQuery_of_ne, hl]
    · simp [QueryCache.cacheQuery_of_ne, hl, hr]

/-- An unobserved query may be sampled early, whether or not the computation later uses it. -/
theorem evalDist_presample_fresh {α : Type} (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (target : Bytes) (hfresh : cache target = none) :
    𝒟[(simulateQ romImpl computation).run' cache] = 𝒟[do
      let output ← $ᵗ HashOutput
      (simulateQ romImpl computation).run' (cache.cacheQuery target output)] := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value =>
      apply evalDist_ext
      intro result
      simp
  | query_bind input next ih =>
      cases input with
      | inl input =>
          dsimp only [OracleWorld] at next ih ⊢
          have hrun (cache : QueryCache HashSpec) :
              (simulateQ romImpl (liftM (OracleWorld.query (.inl input)) >>= next)).run' cache =
                ((liftM (unifSpec.query input) : ProbComp _) >>= fun answer =>
                  (simulateQ romImpl (next answer)).run' cache) := by
            rw [run'_query_bind]
            change (((fun answer => (answer, cache)) <$> (liftM (unifSpec.query input) : ProbComp _)) >>= _) = _
            exact bind_map_left (m := ProbComp) (fun answer => (answer, cache))
              (liftM (unifSpec.query input) : ProbComp _)
              (fun result => (simulateQ romImpl (next result.1)).run' result.2)
          rw [hrun]
          trans 𝒟[do
            let answer ← (liftM (unifSpec.query input) : ProbComp _)
            let output ← $ᵗ HashOutput
            (simulateQ romImpl (next answer)).run' (cache.cacheQuery target output)]
          · exact evalDist_bind_congr' _ (fun answer => ih answer cache hfresh)
          · rw [evalDist_bind_bind_swap]
            apply evalDist_bind_congr'
            intro output
            rw [hrun]
      | inr input =>
          dsimp only [OracleWorld] at next ih ⊢
          have hrun (cache : QueryCache HashSpec) :
              (simulateQ romImpl (liftM (OracleWorld.query (.inr input)) >>= next)).run' cache =
                ((randomOracle (spec := HashSpec) input).run cache >>= fun result =>
                  (simulateQ romImpl (next result.1)).run' result.2) := run'_query_bind _ _ _
          by_cases heq : input = target
          · subst target
            rw [hrun, QueryImpl.withCaching_run_none _ hfresh, bind_map_left]
            apply evalDist_bind_congr'
            intro output
            rw [hrun, QueryImpl.withCaching_run_some _ (QueryCache.cacheQuery_self _ _ _), pure_bind]
          · have hfresh' (output : HashOutput) : (cache.cacheQuery input output) target = none := by
              rw [QueryCache.cacheQuery_of_ne _ _ (Ne.symm heq), hfresh]
            cases hinput : cache input with
            | some answer =>
                rw [hrun, QueryImpl.withCaching_run_some _ hinput, pure_bind, ih answer cache hfresh]
                apply evalDist_bind_congr'
                intro output
                rw [hrun, QueryImpl.withCaching_run_some _ (by
                  rw [QueryCache.cacheQuery_of_ne _ _ heq, hinput]), pure_bind]
            | none =>
                rw [hrun, QueryImpl.withCaching_run_none _ hinput, bind_map_left]
                trans 𝒟[do
                  let answer ← $ᵗ HashOutput
                  let output ← $ᵗ HashOutput
                  (simulateQ romImpl (next answer)).run' ((cache.cacheQuery input answer).cacheQuery target output)]
                · exact evalDist_bind_congr' _ (fun answer => ih answer _ (hfresh' answer))
                · rw [evalDist_bind_bind_swap]
                  apply evalDist_bind_congr'
                  intro output
                  rw [hrun, QueryImpl.withCaching_run_none _ (by
                    rw [QueryCache.cacheQuery_of_ne _ _ heq, hinput]), bind_map_left]
                  apply evalDist_bind_congr'
                  intro answer
                  rw [cacheQuery_comm cache input target heq]

theorem evalDist_presample_query {α : Type} (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (target : Bytes) :
    𝒟[(simulateQ romImpl computation).run' cache] =
      𝒟[(randomOracle (spec := HashSpec) target).run cache >>= fun result =>
        (simulateQ romImpl computation).run' result.2] := by
  cases hc : cache target with
  | none =>
      rw [QueryImpl.withCaching_run_none _ hc, bind_map_left]
      exact evalDist_presample_fresh computation cache target hc
  | some output =>
      rw [QueryImpl.withCaching_run_some _ hc, pure_bind]

theorem evalDist_presample_computation {α β : Type} (computation : OracleComp OracleWorld α)
    (preparation : OracleComp OracleWorld β) (cache : QueryCache HashSpec) :
    𝒟[(simulateQ romImpl computation).run' cache] =
      𝒟[(simulateQ romImpl preparation).run cache >>= fun result =>
        (simulateQ romImpl computation).run' result.2] := by
  induction preparation using OracleComp.inductionOn generalizing cache with
  | pure value => simp
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
      trans 𝒟[(romImpl input).run cache >>= fun result =>
        (simulateQ romImpl computation).run' result.2]
      · cases input with
        | inl input =>
            apply evalDist_ext
            intro value
            simp [romImpl, XmssSecurity.RandomOracleModel.impl, unifFwdImpl]
        | inr input => exact evalDist_presample_query computation cache input
      · exact evalDist_bind_congr' _ (fun result => ih result.1 result.2)


/-- Preparation preserves the entire actual security outcome, including the
instrumented signing, direct-hash and verification counters. -/
theorem evalDist_security_after_preparation {β : Type} (adversary : Security.Adversary)
    (preparation : OracleComp OracleWorld β) :
    𝒟[Security.run adversary] =
      𝒟[(simulateQ romImpl preparation).run ∅ >>= fun prepared =>
        (simulateQ romImpl (Security.experiment adversary)).run' prepared.2] :=
  evalDist_presample_computation (Security.experiment adversary) preparation ∅

/-- Every supported warmed cache preserves a support-wise property of the
original continuation. This applies to instrumented query-budget properties. -/
theorem property_after_preparation {α β : Type}
    (computation : OracleComp OracleWorld α) (preparation : OracleComp OracleWorld β)
    (cache : QueryCache HashSpec) (property : α → Prop)
    (hproperty : ∀ result ∈ support ((simulateQ romImpl computation).run' cache),
      property result)
    (prepared : β × QueryCache HashSpec)
    (hprepared : prepared ∈ support ((simulateQ romImpl preparation).run cache)) :
    ∀ result ∈ support ((simulateQ romImpl computation).run' prepared.2), property result := by
  intro result hresult
  apply hproperty result
  rw [mem_support_iff_of_evalDist_eq
    (evalDist_presample_computation computation preparation cache), mem_support_bind_iff]
  exact ⟨prepared, hprepared, hresult⟩

/-- The statement's almost-sure budget transfers to each cache reached by an
unobserved preparation. No budget claim is made for arbitrary hybrid caches. -/
theorem security_budget_after_preparation {β : Type} (adversary : Security.Adversary)
    (q : Nat) (hbudget : Security.HasBudget adversary q)
    (preparation : OracleComp OracleWorld β)
    (prepared : β × QueryCache HashSpec)
    (hprepared : prepared ∈ support ((simulateQ romImpl preparation).run ∅)) :
    ∀ result ∈ support ((simulateQ romImpl (Security.experiment adversary)).run' prepared.2),
      result.counts .signing ≤ signingLimit ∧ result.counts.work ≤ q := by
  apply property_after_preparation (Security.experiment adversary) preparation ∅
    (fun result => result.counts .signing ≤ signingLimit ∧ result.counts.work ≤ q)
    _ prepared hprepared
  exact (probEvent_eq_one_iff.mp hbudget).2

end SlhDsaSecurity.ROMPresampling
