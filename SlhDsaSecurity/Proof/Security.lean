import SlhDsaSecurity.Statement.Security

/-! The two notions use the same transcript, verification, and query budgets. -/

open OracleComp OracleSpec

namespace SlhDsaSecurity.Security

theorem fresh_standard_implies_strong (signed : SigningLog) (forgery : Forgery)
    (h : Fresh .standard signed forgery) : Fresh .strong signed forgery := by
  rintro ⟨entry, hentry, hmessage, _⟩
  exact h ⟨entry, hentry, hmessage⟩

theorem advantage_standard_le_strong (adversary : Adversary) :
    advantage .standard adversary ≤ advantage .strong adversary := by
  apply probEvent_mono''
  intro outcome h
  exact ⟨h.1, fresh_standard_implies_strong outcome.signed outcome.forgery h.2⟩

/-! ## The all-queries-counted statements agree with the verifier-counted ones

Instrumenting the experiment with a total hash count does not disturb it: the count is
extra bookkeeping carried alongside the outcome, so projecting it away recovers the
original run. Every result already proved about `run` and `advantage` therefore transfers
to `runAll` and `totalAdvantage`.
-/

theorem fst_map_countAllHashes {α : Type} (computation : OracleComp OracleWorld α) :
    Prod.fst <$> countAllHashes computation = computation := by
  unfold countAllHashes
  rw [Functor.map_map]
  exact fst_map_run_simulateQ_addCostOracle hashCost computation

theorem fst_map_runAll (adversary : Adversary) :
    Prod.fst <$> runAll adversary = run adversary := by
  have hkey : simulateQ (Xmss.RandomOracleModel.impl Bytes HashOutput)
      (experiment adversary) =
      Prod.fst <$> simulateQ (Xmss.RandomOracleModel.impl Bytes HashOutput)
        (countAllHashes (experiment adversary)) := by
    rw [← simulateQ_map, fst_map_countAllHashes]
  unfold runAll run Xmss.RandomOracleModel.run
  rw [hkey]
  simp [StateT.run'_eq, StateT.run_map, Functor.map_map]

/-- The all-counted advantage is the verifier-counted advantage: the counter is bookkeeping. -/
theorem totalAdvantage_eq (notion : Notion) (adversary : Adversary) :
    totalAdvantage notion adversary = advantage notion adversary := by
  unfold totalAdvantage advantage
  rw [show (fun result : Outcome × Nat => Wins notion result.1) =
    Wins notion ∘ Prod.fst from rfl, ← probEvent_map, fst_map_runAll]

theorem totalAdvantage_standard_le_strong (adversary : Adversary) :
    totalAdvantage .standard adversary ≤ totalAdvantage .strong adversary := by
  rw [totalAdvantage_eq, totalAdvantage_eq]
  exact advantage_standard_le_strong adversary

end SlhDsaSecurity.Security
