import XmssSecurity.Proof.TargetSum.EUFCMA.Execution
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! The statement's semantic direct-query bound permits pruning without changing
the standard-forgery probability. Subsequent bounds may use syntactic adversaries. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.EUFCMA
open XmssSecurity.EUFCMA

open Generic.Direct

attribute [local irreducible] Generic.sampleMasterSeed

theorem direct_queryBound_iff_strong_legacy (adversary : Generic.Security.StatementAdversary) (D : ℕ) :
    (notion SUFCMA.CountingMode.direct).HasQueryBound Generic.xmss adversary D ↔
      SUFCMA.notionDirect.HasQueryBound Generic.xmss adversary D :=
  (hasQueryBound_iff_strong _ _ _ _).trans (Modes.notion_direct_hasQueryBound_iff _ _ _)

theorem forgeAdvantage_prune_eq (adversary : Generic.Security.StatementAdversary) (D : ℕ)
    (hD : (notion SUFCMA.CountingMode.direct).HasQueryBound Generic.xmss adversary D) :
    forgeAdvantage Generic.Seeded.scheme (Generic.Security.embed adversary) =
      forgeAdvantage Generic.Seeded.scheme (Generic.Direct.pruneAdversary D (Generic.Security.embed adversary)) := by
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
  have hprune := Generic.Direct.simulateQ_pruneDirect_eq_logged (Generic.Security.adversaryImpl secretKey)
    (adversary.main publicKey) D cache
    (fun result hresult => by
      rcases result with ⟨⟨⟨forgery, charged⟩, log⟩, cache'⟩
      exact Generic.Security.adversary_counted_bound adversary D hstrong publicKey secretKey cache hkeys
        forgery charged log cache' hresult)
  exact congrArg (fun computation => computation >>= _) hprune.symm

/-- A bound for syntactically bounded standard adversaries proves the statement. -/
theorem direct_security_of_isDirectQueryBound (bits : ℕ)
    (h : ∀ (adversary : Generic.Adversary) (D : ℕ), 1 ≤ D → Generic.Direct.IsDirectQueryBound adversary D →
      forgeAdvantage Generic.Seeded.scheme adversary ≤ D / ((2 ^ bits : ℕ) : ℝ≥0∞)) :
    (notion SUFCMA.CountingMode.direct).HasClassicalSecurityBits Generic.xmss bits := by
  intro D hD adversary hbound
  rw [notion_advantage_eq, forgeAdvantage_prune_eq adversary D hbound]
  exact h _ D hD (Generic.Direct.pruneAdversary_isDirectQueryBound D (Generic.Security.embed adversary))

/-- info: 'XmssSecurity.TargetSum.EUFCMA.direct_security_of_isDirectQueryBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms direct_security_of_isDirectQueryBound

end XmssSecurity.TargetSum.EUFCMA
