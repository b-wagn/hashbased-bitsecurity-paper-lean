import XmssSecurity.Proof.Checksum.Attack.NeighborSeeded
import XmssSecurity.Proof.Checksum.ExactKeygenQueryCount

/-! Worst-case hash budgets for the honest stages surrounding the neighboring-signature attack. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.Checksum.Attack

open Concrete

attribute [local irreducible] sampleMasterSeed

theorem exactQueryCount_isQueryBoundP {ι α : Type} {spec : OracleSpec ι}
    {computation : OracleComp spec α} {count : ℕ} (hexact : ExactQueryCount computation count) :
    computation.IsQueryBoundP (fun _ => True) count := by
  induction hexact with
  | pure value => simp
  | query input next count hnext ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff]
      exact ⟨Or.inr (by omega), fun output => by simpa using ih output⟩

theorem deriveKey_queryBound (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) :
    (deriveKey parameter domain seed : OracleComp HashSpec Digest).IsQueryBoundP (fun _ => True) 1 := by
  unfold deriveKey oracleHash
  simp

theorem deriveRandomizer_queryBound (parameter : PublicParameter) (seed : MasterSeed)
    (leafIndex : LeafIndex) (message : Message) (trial : BitVec 32) :
    (deriveRandomizer parameter seed leafIndex message trial : OracleComp HashSpec Randomness).IsQueryBoundP
      (fun _ => True) 1 := by
  unfold deriveRandomizer oracleHash
  simp

def seededKeygenQueryBudget : ℕ := 1 + (lifetime * numChains + treeHashQueryCount treeHeight)

theorem seededKeygenFromSeed_queryBound (seed : MasterSeed) :
    (Seeded.keygenFromSeed seed).IsQueryBoundP (fun _ => True) seededKeygenQueryBudget := by
  unfold Seeded.keygenFromSeed seededKeygenQueryBudget
  refine OracleComp.isQueryBoundP_bind (deriveKey_queryBound _ _ _) ?_
  intro parameter _
  refine OracleComp.isQueryBoundP_bind (n := lifetime * numChains) (m := treeHashQueryCount treeHeight) ?_ ?_
  · have hbound := Direct.sequenceFin_isQueryBoundP
      (fun leafIndex : LeafIndex => sequenceFin fun chain : ChainIndex =>
        (deriveKey parameter (.chain leafIndex chain) seed : OracleComp HashSpec Digest))
      (fun _ => numChains) (fun _ => True) (fun leafIndex => by
        simpa using Direct.sequenceFin_isQueryBoundP
          (fun chain : ChainIndex => (deriveKey parameter (.chain leafIndex chain) seed : OracleComp HashSpec Digest))
          (fun _ => 1) (fun _ => True) (fun chain => deriveKey_queryBound _ _ _))
    simpa using hbound
  · intro secret _
    simp only [bind_pure_comp, OracleComp.isQueryBoundP_map_iff]
    exact exactQueryCount_isQueryBoundP ((ExactQueryCount.rootTree parameter secret).withQueryLog)

theorem xmss_keygen_queryBound : xmss.keygen.IsQueryBoundP IsHashQuery seededKeygenQueryBudget := by
  change ((liftM sampleMasterSeed : OracleComp OracleWorld MasterSeed) >>= fun seed =>
    liftM (Seeded.keygenFromSeed seed)).IsQueryBoundP _ _
  rw [← Nat.zero_add seededKeygenQueryBudget]
  refine OracleComp.isQueryBoundP_bind ?_ ?_
  · exact OracleComp.IsQueryBoundP.liftComp_subSpec (p := fun _ : unifSpec.Domain => False) (q := IsHashQuery)
      (fun _ => by simp [IsHashQuery]) (OracleComp.isQueryBoundP_false sampleMasterSeed 0)
  · intro seed _
    exact OracleComp.IsQueryBoundP.liftComp_subSpec (p := fun _ => True) (q := IsHashQuery)
      (fun input => by change True ↔ IsHashQuery (.inr input); simp [IsHashQuery])
      (seededKeygenFromSeed_queryBound seed)

theorem precomputedSignAttempt_queryBound (secretKey : SecretKey) (leafIndex : LeafIndex)
    (message : Message) (randomness : Randomness) :
    (precomputedSignAttempt secretKey leafIndex message randomness : OracleComp HashSpec (Option Signature)).IsQueryBoundP
      (fun _ => True) 1 := by
  unfold precomputedSignAttempt
  rw [← Nat.add_zero 1]
  refine OracleComp.isQueryBoundP_bind (Direct.tweakableHash_isQueryBoundP _ _ _) ?_
  intro digest _
  split <;> exact OracleComp.isQueryBoundP_pure _ _ _

theorem seededSignFrom_queryBound (secretKey : Seeded.SecretKey) (leafIndex : LeafIndex)
    (message : Message) (attempts trial : ℕ) :
    (Seeded.signFrom secretKey leafIndex message attempts trial : OracleComp HashSpec (Option Signature)).IsQueryBoundP
      (fun _ => True) (attempts * 2) := by
  induction attempts generalizing trial with
  | zero => simp [Seeded.signFrom]
  | succ attempts ih =>
      rw [show (attempts + 1) * 2 = 1 + (1 + attempts * 2) by omega, Seeded.signFrom]
      refine OracleComp.isQueryBoundP_bind (deriveRandomizer_queryBound _ _ _ _ _) ?_
      intro randomness _
      refine OracleComp.isQueryBoundP_bind (precomputedSignAttempt_queryBound _ _ _ _) ?_
      intro answer _
      cases answer with
      | none => exact ih _
      | some signature => exact OracleComp.isQueryBoundP_pure _ _ _

theorem xmss_sign_queryBound (secretKey : Seeded.SecretKey) (leafIndex : LeafIndex) (message : Message) :
    (xmss.sign secretKey leafIndex message).IsQueryBoundP IsHashQuery (signingAttemptLimit * 2) := by
  change (liftComp (Seeded.sign secretKey leafIndex message : OracleComp HashSpec (Option Signature))
    OracleWorld).IsQueryBoundP _ _
  rw [Seeded.sign_eq_signFrom]
  exact OracleComp.IsQueryBoundP.liftComp_subSpec (p := fun _ => True) (q := IsHashQuery)
    (fun input => by change True ↔ IsHashQuery (.inr input); simp [IsHashQuery])
    (seededSignFrom_queryBound secretKey leafIndex message signingAttemptLimit 0)

theorem seededKeygenQueryBudget_le : seededKeygenQueryBudget ≤ 2 ^ 42 := by
  norm_num [seededKeygenQueryBudget, treeHashQueryCount, treeHeight, lifetime, numChains, chainLength, winternitzBits]

def neighborEverythingBudget : ℕ := 2 ^ 126 + 2 ^ 124 + 2 ^ 120

theorem neighbor_total_budget_le :
    seededKeygenQueryBudget + (signingAttemptLimit * 2 + neighborDirectBudget) + Direct.verifierQueryBound + 1 ≤
      neighborEverythingBudget := by
  apply le_trans (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_right seededKeygenQueryBudget_le _) _) _) ?_
  norm_num [neighborEverythingBudget, neighborDirectBudget, neighborSearchSteps, preimageSearchSteps,
    signingAttemptLimit, Direct.verifierQueryBound, verificationChainHashes, treeHeight,
    numChains, chainLength, winternitzBits]

theorem neighborEverythingBudget_ratio :
    (neighborEverythingBudget : ℝ≥0∞) / ((2 ^ 128 : ℕ) : ℝ≥0∞) = 81 / 256 := by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [neighborEverythingBudget, ENNReal.toReal_div]

/-- info: 'XmssSecurity.Checksum.Attack.xmss_keygen_queryBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_keygen_queryBound

/-- info: 'XmssSecurity.Checksum.Attack.xmss_sign_queryBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_sign_queryBound

end XmssSecurity.Checksum.Attack
