import Xmss.Proof.Generic.Seeded.BudgetTransfer
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability
/-! A computation that never queries a protected input has the same supported answers
under caches that agree elsewhere. The final caches still agree outside the protected set. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum.Seeded

theorem randomOracle_support_transfer_of_agreeOutside
    (bad : HashInput → Prop) (left right : QueryCache HashSpec)
    (hagree : Seeded.AgreeOutside bad left right) (input : HashInput) (hinput : ¬bad input)
    (result : Digest × QueryCache HashSpec)
    (hresult : result ∈ support ((randomOracle (spec := HashSpec) input).run right)) :
    ∃ cache, (result.1, cache) ∈ support ((randomOracle (spec := HashSpec) input).run left) ∧
      Seeded.AgreeOutside bad cache result.2 := by
  have hcache := Seeded.romImpl_support_cacheAfter (.inr input) right result hresult
  rcases result with ⟨answer, cache⟩
  dsimp only at hcache
  subst cache
  exact ⟨Seeded.cacheAfter left (.inr input) answer,
    Seeded.romImpl_support_transfer bad left right hagree (.inr input) hinput answer hresult⟩

theorem support_transfer_of_no_protected_queries {α : Type}
    (bad : HashInput → Prop) [DecidablePred bad] (computation : OracleComp HashSpec α)
    (hqueries : computation.IsQueryBoundP bad 0)
    (left right : QueryCache HashSpec) (hagree : Seeded.AgreeOutside bad left right)
    (result : α × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ randomOracle computation).run right)) :
    ∃ cache, (result.1, cache) ∈ support ((simulateQ randomOracle computation).run left) ∧
      Seeded.AgreeOutside bad cache result.2 := by
  induction computation using OracleComp.inductionOn generalizing left right result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hresult
      subst result
      exact ⟨left, by simp, hagree⟩
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hqueries
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        mem_support_bind_iff] at hresult ⊢
      obtain ⟨step, hstep, htail⟩ := hresult
      have hinput : ¬bad input := by
        intro hbad
        simp [hbad] at hqueries
      obtain ⟨nextCache, hnext, hnextAgree⟩ :=
        randomOracle_support_transfer_of_agreeOutside bad left right hagree input hinput step hstep
      obtain ⟨finalCache, hfinal, hfinalAgree⟩ :=
        ih step.1 (by simpa [hinput] using hqueries.2 step.1)
          nextCache step.2 hnextAgree result htail
      exact ⟨finalCache, ⟨(step.1, nextCache), hnext, hfinal⟩, hfinalAgree⟩

end Xmss.TargetSum.Seeded
