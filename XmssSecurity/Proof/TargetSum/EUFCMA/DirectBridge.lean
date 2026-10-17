import XmssSecurity.Proof.TargetSum.EUFCMA.Execution

/-! The statement's semantic direct-query bound permits pruning without changing
the standard-forgery probability. Subsequent bounds may use syntactic adversaries. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.EUFCMA
open XmssSecurity.EUFCMA

open Direct

attribute [local irreducible] sampleMasterSeed

theorem direct_queryBound_iff_strong_legacy (adversary : Security.StatementAdversary) (D : ℕ) :
    (notion SUFCMA.CountingMode.direct).HasQueryBound xmss adversary D ↔
      SUFCMA.notionDirect.HasQueryBound xmss adversary D :=
  (hasQueryBound_iff_strong _ _ _ _).trans (Modes.notion_direct_hasQueryBound_iff _ _ _)

theorem forgeAdvantage_prune_eq (adversary : Security.StatementAdversary) (D : ℕ)
    (hD : (notion SUFCMA.CountingMode.direct).HasQueryBound xmss adversary D) :
    forgeAdvantage Seeded.scheme (Security.embed adversary) =
      forgeAdvantage Seeded.scheme (pruneAdversary D (Security.embed adversary)) := by
  have hstrong := (direct_queryBound_iff_strong_legacy adversary D).1 hD
  unfold forgeAdvantage
  refine congrArg (fun computation => Pr[= true | computation]) ?_
  unfold gameCore
  simp only [simulateQ_bind, StateT.run'_bind']
  refine bind_congr_of_forall_mem_support _ fun keys hkeys => ?_
  rcases keys with ⟨⟨publicKey, secretKey⟩, cache⟩
  dsimp only
  unfold gameRest
  simp only [simulateQ_bind, StateT.run'_bind']
  have hprune := simulateQ_pruneDirect_eq_logged (Security.adversaryImpl secretKey)
    (adversary.main publicKey) D cache
    (fun result hresult => by
      rcases result with ⟨⟨⟨forgery, charged⟩, log⟩, cache'⟩
      exact Security.adversary_counted_bound adversary D hstrong publicKey secretKey cache hkeys
        forgery charged log cache' hresult)
  exact congrArg (fun computation => computation >>= _) hprune.symm

/-- A bound for syntactically bounded standard adversaries proves the statement. -/
theorem direct_security_of_isDirectQueryBound (bits : ℕ)
    (h : ∀ (adversary : XmssSecurity.TargetSum.Adversary) (D : ℕ), 1 ≤ D → IsDirectQueryBound adversary D →
      forgeAdvantage Seeded.scheme adversary ≤ D / ((2 ^ bits : ℕ) : ℝ≥0∞)) :
    (notion SUFCMA.CountingMode.direct).HasClassicalSecurityBits xmss bits := by
  intro D hD adversary hbound
  rw [notion_advantage_eq, forgeAdvantage_prune_eq adversary D hbound]
  exact h _ D hD (pruneAdversary_isDirectQueryBound D (Security.embed adversary))

/-- info: 'XmssSecurity.TargetSum.EUFCMA.direct_security_of_isDirectQueryBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms direct_security_of_isDirectQueryBound

end XmssSecurity.TargetSum.EUFCMA
