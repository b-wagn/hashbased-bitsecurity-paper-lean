import Xmss.Proof.TargetSum.Direct.SharedDecidingBudget
import Xmss.Proof.Common.Modes.Direct
import Xmss.Proof.Common.Modes.Lattice
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! Security when direct queries and key generation are charged. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

open Xmss.Generic

namespace Xmss.TargetSum

attribute [local irreducible] Generic.sampleMasterSeed

def seededKeygenQueryCount : ℕ :=
  1 + lifetime * numChains + treeHashQueryCount treeHeight

theorem exactQueryCount_deriveKey (parameter : PublicParameter) (domain : Generic.KeygenDomain)
    (seed : MasterSeed) :
    ExactQueryCount (Generic.deriveKey parameter domain seed : OracleComp HashSpec Digest) 1 := by
  exact ExactQueryCount.oracleHash _

theorem exactQueryCount_seededKeygenFromSeed (seed : MasterSeed) :
    ExactQueryCount (Generic.Seeded.keygenFromSeed seed) seededKeygenQueryCount := by
  have hchains (parameter : PublicParameter) : ExactQueryCount
      (Generic.sequenceFin fun leafIndex => Generic.sequenceFin fun chain =>
        (Generic.deriveKey parameter (.chain leafIndex chain) seed : OracleComp HashSpec Digest))
      (lifetime * numChains) := by
    have hinner (leafIndex : LeafIndex) := ExactQueryCount.sequenceFin
      (fun chain : ChainIndex => (Generic.deriveKey parameter (.chain leafIndex chain) seed :
        OracleComp HashSpec Digest)) (fun _ => 1)
      (fun chain => exactQueryCount_deriveKey parameter (.chain leafIndex chain) seed)
    have houter := ExactQueryCount.sequenceFin
      (fun leafIndex : LeafIndex => Generic.sequenceFin fun chain =>
        (Generic.deriveKey parameter (.chain leafIndex chain) seed : OracleComp HashSpec Digest))
      (fun _ => numChains) (fun leafIndex => by simpa using hinner leafIndex)
    simpa using houter
  unfold Generic.Seeded.keygenFromSeed seededKeygenQueryCount
  simpa only [Nat.add_assoc, Nat.add_zero] using
    (exactQueryCount_deriveKey 0 .parameter seed).bind _
      (lifetime * numChains + treeHashQueryCount treeHeight) (fun parameter =>
        (hchains parameter).bind _ (treeHashQueryCount treeHeight) (fun secret =>
          (ExactQueryCount.withQueryLog (ExactQueryCount.rootTree parameter secret)).bind _ 0
            (fun result => ExactQueryCount.pure _)))

theorem exactPredicateQueryCount_xmss_keygen :
    ExactPredicateQueryCount IsHashQuery Generic.xmss.keygen seededKeygenQueryCount := by
  change ExactPredicateQueryCount IsHashQuery
    ((liftM Generic.sampleMasterSeed : OracleComp OracleWorld MasterSeed) >>= fun seed =>
      liftM (Generic.Seeded.keygenFromSeed seed)) seededKeygenQueryCount
  refine ExactQueryCount.ExactPredicateQueryCount.bind
    (ExactQueryCount.ExactPredicateQueryCount.liftProbComp_hashCount_zero Generic.sampleMasterSeed) _
    seededKeygenQueryCount ?_
  intro seed
  change ExactPredicateQueryCount IsHashQuery
    (OracleComp.liftComp (Generic.Seeded.keygenFromSeed seed) OracleWorld) seededKeygenQueryCount
  exact ExactQueryCount.liftComp_predicate (exactQueryCount_seededKeygenFromSeed seed)
    IsHashQuery (fun input => by
      change IsHashQuery (.inr input)
      simp [IsHashQuery])

namespace Modes
open Xmss.Modes

theorem charge_hashCost_eq_countHashQueries (computation : OracleComp OracleWorld α) :
    Unforgeability.charge (RandomOracleModel.hashCost HashInput Digest) computation =
      countHashQueries computation := by
  unfold Unforgeability.charge addCostOracle countHashQueries
  have hcost : RandomOracleModel.hashCost HashInput Digest =
      fun input : OracleWorld.Domain => if input matches .inr _ then 1 else 0 := by
    funext input
    cases input <;> rfl
  rw [hcost, ← QueryCounting.simulate_withCost]
  simp only [QueryImpl.ofLift_eq_id', simulateQ_id']
  change id <$> QueryCounting.counted (fun input : OracleWorld.Domain => input matches .inr _)
    computation = _
  rw [id_map]
  rfl

theorem charge_xmss_keygen :
    Unforgeability.charge (RandomOracleModel.hashCost HashInput Digest) Generic.xmss.keygen =
      (fun keys => (keys, seededKeygenQueryCount)) <$> Generic.xmss.keygen := by
  rw [charge_hashCost_eq_countHashQueries]
  exact countHashQueries_of_exact exactPredicateQueryCount_xmss_keygen

theorem gameCounted_keygen_eq
    {ι : Type} {spec : OracleSpec ι} {PK SK Msg Sig : Type} {L : ℕ}
    [DecidableEq Msg] [DecidableEq Sig] (cost : spec.Domain → ℕ)
    (scheme : EpochBasedSignature spec PK SK Msg Sig L)
    (adversary : Unforgeability.Adversary spec PK Msg Sig L) (K : ℕ)
    (hkeygen : Unforgeability.charge cost scheme.keygen = (fun keys => (keys, K)) <$> scheme.keygen) :
    SUFCMA.gameCounted ⟨true, false, false, false⟩ cost scheme adversary =
      (fun result => (result.1, K + result.2)) <$>
        SUFCMA.gameCountedDirect cost scheme adversary := by
  unfold SUFCMA.gameCounted SUFCMA.gameCountedDirect
  simp only [Unforgeability.costIf, Bool.false_eq_true, if_true, if_false, hkeygen, charge_zero, impl_direct_eq,
    bind_map_left, map_bind, map_pure, add_zero]
  rfl

theorem notion_keygen_experiment_eq (adversary : AdversaryBridge.StatementAdversary) :
    (SUFCMA.notion ⟨true, false, false, false⟩).experiment Generic.xmss adversary =
      (fun result => (result.1, seededKeygenQueryCount + result.2)) <$>
        SUFCMA.notionDirect.experiment Generic.xmss adversary := by
  simp only [SUFCMA.notion, SUFCMA.notionDirect, RandomOracleModel.run]
  rw [gameCounted_keygen_eq _ _ _ _ charge_xmss_keygen, simulateQ_map, StateT.run'_map']
  rfl

theorem direct_hasQueryBound_sub_keygen (adversary : AdversaryBridge.StatementAdversary) (q : ℕ)
    (hbound : (SUFCMA.notion ⟨true, false, false, false⟩).HasQueryBound Generic.xmss adversary q) :
    SUFCMA.notionDirect.HasQueryBound Generic.xmss adversary (q - seededKeygenQueryCount) := by
  intro result hresult
  have h := hbound (result.1, seededKeygenQueryCount + result.2) (by
    rw [notion_keygen_experiment_eq, support_map]
    exact ⟨result, hresult, rfl⟩)
  dsimp only at h
  omega

theorem keygenQueryCount_le_queryBound (adversary : AdversaryBridge.StatementAdversary) (q : ℕ)
    (hbound : (SUFCMA.notion ⟨true, false, false, false⟩).HasQueryBound Generic.xmss adversary q) :
    seededKeygenQueryCount ≤ q := by
  obtain ⟨result, hresult⟩ := probComp_support_nonempty (SUFCMA.notionDirect.experiment Generic.xmss adversary)
  have h := hbound (result.1, seededKeygenQueryCount + result.2) (by
    rw [notion_keygen_experiment_eq, support_map]
    exact ⟨result, hresult, rfl⟩)
  dsimp only at h
  omega

theorem twentySix_le_seededKeygenQueryCount : 26 ≤ seededKeygenQueryCount := by
  have h := treeHashQueryCount_base_le treeHeight
  norm_num [numChains, chainLength, winternitzBits] at h
  unfold seededKeygenQueryCount
  omega

theorem sharedDecidingLoss_le_127_of_gap (D q : ℕ) (hgap : D + 26 ≤ q)
    (hsmall : q ≤ 2 ^ 127) :
    Direct.sharedDecidingLoss D ≤ (q : ℝ≥0∞) / ((2 ^ 127 : ℕ) : ℝ≥0∞) := by
  have hgap' : (D : ℝ) + 26 ≤ q := by exact_mod_cast hgap
  have hsmall' : (q : ℝ) ≤ 2 ^ 127 := by exact_mod_cast hsmall
  unfold Direct.sharedDecidingLoss
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_natCast, Nat.cast_add, Nat.cast_mul]
  simp only [digestBits]
  push_cast
  linarith

/-- Charging key generation as well as the adversary's direct queries gives 127-bit security. -/
theorem sufCmaKeygen_127 :
    (SUFCMA.notion ⟨true, false, false, false⟩).HasClassicalSecurityBits Generic.xmss 127 := by
  intro q _hq adversary hbound
  by_cases hlarge : 2 ^ 127 ≤ q
  · calc
      _ ≤ 1 := probEvent_le_one
      _ = ((2 ^ 127 : ℕ) : ℝ≥0∞) / ((2 ^ 127 : ℕ) : ℝ≥0∞) :=
        (ENNReal.div_self (by norm_num) (ENNReal.natCast_ne_top _)).symm
      _ ≤ _ := by gcongr
  · have hkeygen := keygenQueryCount_le_queryBound adversary q hbound
    have hdirect := direct_hasQueryBound_sub_keygen adversary q hbound
    rw [advantage_eq_of_mode _ Unforgeability.CountingMode.direct,
      notion_direct_advantage_eq, AdversaryBridge.notionDirect_advantage_eq,
      AdversaryBridge.forgeAdvantage_prune_eq adversary (q - seededKeygenQueryCount) hdirect]
    refine (Direct.seeded_forgeAdvantage_le_sharedDecidingLoss _ _
      (Direct.pruneAdversary_isDirectQueryBound _ (AdversaryBridge.embed adversary))
        (by have := twentySix_le_seededKeygenQueryCount; omega)).trans
        (sharedDecidingLoss_le_127_of_gap _ q ?_ (by omega))
    have := twentySix_le_seededKeygenQueryCount
    omega

end Modes
end Xmss.TargetSum
