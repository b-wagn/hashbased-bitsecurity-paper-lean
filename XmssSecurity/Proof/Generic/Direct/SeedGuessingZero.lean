import XmssSecurity.Proof.Generic.Direct.SeedGuessing

/-! Without direct hash queries, seed-derivation cache entries have no effect on the game. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.Generic.Seeded

variable [Code]

theorem run'_cache_change_eq_of_zero {α : Type} (bad : HashInput → Prop) [DecidablePred bad]
    (computation : OracleComp OracleWorld α) (left right : QueryCache HashSpec)
    (hagree : AgreeOutside bad left right)
    (hbound : computation.IsQueryBoundP (hashBad bad) 0) :
    (simulateQ romImpl computation).run' left = (simulateQ romImpl computation).run' right := by
  induction computation using OracleComp.inductionOn generalizing left right with
  | pure value => simp
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      have hbad : ¬hashBad bad input := by simpa using hbound.1
      have hnext : ∀ answer, (next answer).IsQueryBoundP (hashBad bad) 0 := by
        intro answer
        simpa using hbound.2 answer
      rw [run'_query_bind, run'_query_bind]
      cases input with
      | inl input =>
          dsimp [OracleWorld] at next ih ⊢
          change ((fun answer => (answer, left)) <$> (liftM (unifSpec.query input) : ProbComp _) >>= _) =
            ((fun answer => (answer, right)) <$> (liftM (unifSpec.query input) : ProbComp _) >>= _)
          simp only [bind_map_left]
          apply bind_congr
          intro answer
          exact ih answer left right hagree (hnext answer)
      | inr input =>
          dsimp [OracleWorld] at next ih ⊢
          change ((randomOracle input).run left >>= _) = ((randomOracle input).run right >>= _)
          have heq := hagree input hbad
          cases hleft : left input with
          | none =>
              have hright : right input = none := heq.symm.trans hleft
              rw [QueryImpl.withCaching_run_none _ hleft, QueryImpl.withCaching_run_none _ hright]
              simp only [bind_map_left]
              apply bind_congr
              intro answer
              exact ih answer _ _ (hagree.cacheQuery input answer) (hnext answer)
          | some answer =>
              have hright : right input = some answer := heq.symm.trans hleft
              rw [QueryImpl.withCaching_run_some _ hleft, QueryImpl.withCaching_run_some _ hright]
              simp only [pure_bind]
              exact ih answer left right hagree (hnext answer)

theorem evalDist_deterministic_eq_table_of_noSeed (adversary : Adversary)
    (hbound : ∀ parameter secret randomizers,
      (tableGameAfterSecrets adversary parameter secret randomizers).IsQueryBoundP (hashBad MaySeedHit) 0) :
    evalDist ((simulateQ romImpl (gameCore scheme adversary)).run' ∅) =
      evalDist (independentTableGame adversary) := by
  rw [evalDist_gameCore_deterministic_programmed, evalDist_programmedDeterministicGame_seed_last]
  unfold independentTableGame
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro material
  have hrun : ∀ seed,
      (simulateQ romImpl (tableGameAfterSecrets adversary (truncateHash material.1)
        (outputSecrets material.2.1) material.2.2)).run'
          (signingDerivationCache seed material.1 material.2.1 material.2.2) =
      (simulateQ romImpl (tableGameAfterSecrets adversary (truncateHash material.1)
        (outputSecrets material.2.1) material.2.2)).run' ∅ := by
    intro seed
    apply run'_cache_change_eq_of_zero MaySeedHit
    · intro input hinput
      apply signingDerivationCache_agreeOutside_derivationHit seed _ _ _ input
      intro hhit
      exact hinput hhit.2
    · exact hbound _ _ _
  simp_rw [hrun]
  apply evalDist_ext
  intro result
  simp

theorem evalDist_deterministic_eq_table_of_direct_zero (adversary : Adversary)
    (hbound : Direct.IsDirectQueryBound adversary 0) :
    evalDist ((simulateQ romImpl (gameCore scheme adversary)).run' ∅) =
      evalDist (independentTableGame adversary) :=
  evalDist_deterministic_eq_table_of_noSeed adversary
    (fun _ _ _ => tableGameAfterSecrets_bound adversary 0 hbound _ _ _)

/-- info: 'XmssSecurity.Generic.Seeded.evalDist_deterministic_eq_table_of_direct_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalDist_deterministic_eq_table_of_direct_zero

end XmssSecurity.Generic.Seeded
