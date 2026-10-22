import Xmss.Proof.Generic.ExpectedAdaptiveFreshTarget
import Xmss.Proof.Generic.Execution
import Xmss.Proof.Checksum.Code
import Xmss.Proof.Checksum.EncodingProbability
/-!
# Hiding a cache from a computation

A computation run in the random-oracle model from the union of a cache `hidden` and a disjoint
cache `cache` behaves as the same computation run from `cache` alone until it queries an entry of
`hidden`. Hence any event of its result is at most as likely as the same event, or a query of
`hidden`, in the run from `cache` (`probEvent_run_unionCache_le`). The run from `cache` does not
depend on `hidden`, which is what the no-signature bound uses for the key-generation cache.
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.Checksum.HiddenSibling

/-- The entries of `hidden`, and those of `cache` at the other inputs. -/
def unionCache (hidden cache : QueryCache HashSpec) : QueryCache HashSpec :=
  fun input => match hidden input with
    | some output => some output
    | none => cache input

theorem unionCache_empty (hidden : QueryCache HashSpec) :
    unionCache hidden ∅ = hidden := by
  funext input
  unfold unionCache
  cases hidden input <;> rfl

theorem unionCache_of_none (hidden cache : QueryCache HashSpec) (input : HashInput)
    (hnone : hidden input = none) : unionCache hidden cache input = cache input := by
  simp [unionCache, hnone]

theorem unionCache_cacheQuery (hidden cache : QueryCache HashSpec) (input : HashInput)
    (output : Digest) (hnone : hidden input = none) :
    (unionCache hidden cache).cacheQuery input output =
      unionCache hidden (cache.cacheQuery input output) := by
  funext candidate
  by_cases heq : candidate = input
  · subst candidate
    simp [unionCache, hnone]
  · rw [QueryCache.cacheQuery_of_ne _ _ heq]
    unfold unionCache
    cases hidden candidate <;> simp [QueryCache.cacheQuery_of_ne _ _ heq]

/-- The run queried an entry of `hidden`. -/
def HitsCache (hidden finalCache : QueryCache HashSpec) : Prop :=
  ∃ input, finalCache input ≠ none ∧ hidden input ≠ none

theorem probEvent_run_unionCache_le {α : Type} (computation : OracleComp OracleWorld α)
    (hidden cache : QueryCache HashSpec)
    (hdisjoint : ∀ input, hidden input ≠ none → cache input = none)
    (event : α → Prop) :
    Pr[fun result => event result.1 |
        (simulateQ romImpl computation).run (unionCache hidden cache)] ≤
      Pr[fun result => event result.1 ∨ HitsCache hidden result.2 |
        (simulateQ romImpl computation).run cache] := by
  classical
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, probEvent_pure]
      split_ifs with hleft hright
      · exact le_rfl
      · exact absurd (Or.inl hleft) hright
      · exact zero_le
      · exact le_rfl
  | query_bind query next ih =>
      rcases query with uniformIndex | hashInput
      · change Fin (uniformIndex + 1) → OracleComp OracleWorld α at next
        have hrun : ∀ start : QueryCache HashSpec,
            (simulateQ romImpl
              (liftM (OracleWorld.query (.inl uniformIndex)) >>= next)).run start =
            ((unifSpec.query uniformIndex : ProbComp _) >>= fun sampled =>
              (simulateQ romImpl (next sampled)).run start) := by
          intro start
          simp [StateT.run_bind, romImpl, unifFwdImpl,
            QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply]
        rw [hrun, hrun, probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
        exact ENNReal.tsum_le_tsum fun sampled =>
          mul_le_mul' le_rfl (ih sampled cache hdisjoint)
      · change Digest → OracleComp OracleWorld α at next
        have hcachedRun : ∀ (start : QueryCache HashSpec) (output : Digest),
            start hashInput = some output →
            (simulateQ romImpl
              (liftM (OracleWorld.query (.inr hashInput)) >>= next)).run start =
            (simulateQ romImpl (next output)).run start := by
          intro start output houtput
          have hquery :
              (simulateQ romImpl
                (liftM (OracleWorld.query (.inr hashInput)))).run start =
              pure ((show OracleWorld.Range (.inr hashInput) from output), start) := by
            rw [simulateQ_spec_query]
            change (randomOracle (spec := HashSpec) hashInput).run start = pure (output, start)
            rw [QueryImpl.withCaching_run_some _ houtput]
          rw [simulateQ_bind, StateT.run_bind, hquery, pure_bind]
        have hfreshRun : ∀ start : QueryCache HashSpec, start hashInput = none →
            (simulateQ romImpl
              (liftM (OracleWorld.query (.inr hashInput)) >>= next)).run start =
            (($ᵗ Digest) >>= fun output =>
              (simulateQ romImpl (next output)).run (start.cacheQuery hashInput output)) := by
          intro start hnone
          have hquery :
              (simulateQ romImpl
                (liftM (OracleWorld.query (.inr hashInput)))).run start =
              (($ᵗ Digest) >>= fun output =>
                pure (output, start.cacheQuery hashInput output) : ProbComp _) := by
            rw [simulateQ_spec_query]
            change (randomOracle (spec := HashSpec) hashInput).run start = _
            rw [QueryImpl.withCaching_run_none _ hnone]
            simp [uniformSampleImpl, map_eq_bind_pure_comp]
          rw [simulateQ_bind, StateT.run_bind, hquery]
          simp [monad_norm]
        cases hhidden : hidden hashInput with
        | some hiddenOutput =>
            -- The query hits `hidden`: the run from `cache` records it.
            have hnone : cache hashInput = none := hdisjoint hashInput (by simp [hhidden])
            refine probEvent_le_one.trans (le_of_eq ?_)
            symm
            rw [hfreshRun cache hnone, probEvent_eq_one_iff]
            refine ⟨by simp, fun result hresult => Or.inr ?_⟩
            rw [mem_support_bind_iff] at hresult
            obtain ⟨output, _, hresult⟩ := hresult
            have hle := xmssRom_cache_le (next output) _ result hresult
            refine ⟨hashInput, ?_, by simp [hhidden]⟩
            have hcached : (cache.cacheQuery hashInput output) hashInput = some output := by simp
            rw [hle hcached]
            simp
        | none =>
            cases hcache : cache hashInput with
            | some output =>
                rw [hcachedRun _ output (by rw [unionCache_of_none _ _ _ hhidden, hcache]),
                  hcachedRun _ output hcache]
                exact ih output cache hdisjoint
            | none =>
                rw [hfreshRun _ (by rw [unionCache_of_none _ _ _ hhidden, hcache]),
                  hfreshRun _ hcache, probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
                refine ENNReal.tsum_le_tsum fun output => mul_le_mul' le_rfl ?_
                rw [unionCache_cacheQuery _ _ _ _ hhidden]
                refine ih output _ fun input hinput => ?_
                have hne : input ≠ hashInput := by
                  rintro rfl
                  exact hinput hhidden
                rw [QueryCache.cacheQuery_of_ne _ _ hne]
                exact hdisjoint input hinput

/-- The form used with the key-generation cache: the run from `hidden` against the run from the
empty cache. -/
theorem probEvent_run_le_empty {α : Type} (computation : OracleComp OracleWorld α)
    (hidden : QueryCache HashSpec) (event : α → Prop) :
    Pr[fun result => event result.1 | (simulateQ romImpl computation).run hidden] ≤
      Pr[fun result => event result.1 ∨ HitsCache hidden result.2 |
        (simulateQ romImpl computation).run ∅] := by
  have h := probEvent_run_unionCache_le computation hidden ∅ (fun _ _ => rfl) event
  rwa [unionCache_empty] at h

end Xmss.Checksum.HiddenSibling
