import Xmss.Proof.TargetSum.Attack.NeighborSeeded
import Xmss.Proof.Generic.ExactKeygenQueryCount
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability
/-! Worst-case hash budgets for the honest stages surrounding the neighboring-signature attack. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

open Xmss.Generic

namespace Xmss.TargetSum.Attack

open Hashing Wots Merkle Verify Keygen Signing

attribute [local irreducible] Generic.sampleMasterSeed

theorem exactQueryCount_isQueryBoundP {ι α : Type} {spec : OracleSpec ι}
    {computation : OracleComp spec α} {count : ℕ} (hexact : ExactQueryCount computation count) :
    computation.IsQueryBoundP (fun _ => True) count := by
  induction hexact with
  | pure value => simp
  | query input next count hnext ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff]
      exact ⟨Or.inr (by omega), fun output => by simpa using ih output⟩

theorem deriveKey_queryBound (parameter : PublicParameter) (domain : Generic.KeygenDomain) (seed : MasterSeed) :
    (Generic.deriveKey parameter domain seed : OracleComp HashSpec Digest).IsQueryBoundP (fun _ => True) 1 := by
  unfold Generic.deriveKey Generic.Hashing.oracleHash
  simp

theorem deriveRandomizer_queryBound (parameter : PublicParameter) (seed : MasterSeed)
    (leafIndex : LeafIndex) (message : Message) (trial : BitVec 32) :
    (Generic.deriveRandomizer parameter seed leafIndex message trial : OracleComp HashSpec Randomness).IsQueryBoundP
      (fun _ => True) 1 := by
  unfold Generic.deriveRandomizer Generic.Hashing.oracleHash
  simp

def seededKeygenQueryBudget : ℕ := 1 + (lifetime * numChains + treeHashQueryCount treeHeight)

theorem seededKeygenFromSeed_queryBound (seed : MasterSeed) :
    (Generic.Seeded.keygenFromSeed seed).IsQueryBoundP (fun _ => True) seededKeygenQueryBudget := by
  unfold Generic.Seeded.keygenFromSeed seededKeygenQueryBudget
  refine OracleComp.isQueryBoundP_bind (deriveKey_queryBound _ _ _) ?_
  intro parameter _
  refine OracleComp.isQueryBoundP_bind (n := lifetime * numChains) (m := treeHashQueryCount treeHeight) ?_ ?_
  · have hbound := Direct.sequenceFin_isQueryBoundP
      (fun leafIndex : LeafIndex => Generic.sequenceFin fun chain : ChainIndex =>
        (Generic.deriveKey parameter (.chain leafIndex chain) seed : OracleComp HashSpec Digest))
      (fun _ => numChains) (fun _ => True) (fun leafIndex => by
        simpa using Direct.sequenceFin_isQueryBoundP
          (fun chain : ChainIndex => (Generic.deriveKey parameter (.chain leafIndex chain) seed : OracleComp HashSpec Digest))
          (fun _ => 1) (fun _ => True) (fun chain => deriveKey_queryBound _ _ _))
    simpa using hbound
  · intro secret _
    simp only [bind_pure_comp, OracleComp.isQueryBoundP_map_iff]
    exact exactQueryCount_isQueryBoundP ((ExactQueryCount.rootTree parameter secret).withQueryLog)

theorem xmss_keygen_queryBound : Generic.xmss.keygen.IsQueryBoundP IsHashQuery seededKeygenQueryBudget := by
  change ((liftM Generic.sampleMasterSeed : OracleComp OracleWorld MasterSeed) >>= fun seed =>
    liftM (Generic.Seeded.keygenFromSeed seed)).IsQueryBoundP _ _
  rw [← Nat.zero_add seededKeygenQueryBudget]
  refine OracleComp.isQueryBoundP_bind ?_ ?_
  · exact OracleComp.IsQueryBoundP.liftComp_subSpec (p := fun _ : unifSpec.Domain => False) (q := IsHashQuery)
      (fun _ => by simp [IsHashQuery]) (OracleComp.isQueryBoundP_false Generic.sampleMasterSeed 0)
  · intro seed _
    exact OracleComp.IsQueryBoundP.liftComp_subSpec (p := fun _ => True) (q := IsHashQuery)
      (fun input => by change True ↔ IsHashQuery (.inr input); simp [IsHashQuery])
      (seededKeygenFromSeed_queryBound seed)

theorem precomputedSignAttempt_queryBound (secretKey : Generic.SecretKey) (leafIndex : LeafIndex)
    (message : Message) (randomness : Randomness) :
    (Generic.Signing.precomputedSignAttempt secretKey leafIndex message randomness : OracleComp HashSpec (Option Generic.Signature)).IsQueryBoundP
      (fun _ => True) 1 := by
  unfold Generic.Signing.precomputedSignAttempt
  rw [← Nat.add_zero 1]
  refine OracleComp.isQueryBoundP_bind (Direct.tweakableHash_isQueryBoundP _ _ _) ?_
  intro digest _
  split <;> exact OracleComp.isQueryBoundP_pure _ _ _

theorem seededSignFrom_queryBound (secretKey : Generic.Seeded.SecretKey) (leafIndex : LeafIndex)
    (message : Message) (attempts trial : ℕ) :
    (Generic.Seeded.signFrom secretKey leafIndex message attempts trial : OracleComp HashSpec (Option Generic.Signature)).IsQueryBoundP
      (fun _ => True) (attempts * 2) := by
  induction attempts generalizing trial with
  | zero => simp [Generic.Seeded.signFrom]
  | succ attempts ih =>
      rw [show (attempts + 1) * 2 = 1 + (1 + attempts * 2) by omega, Generic.Seeded.signFrom]
      refine OracleComp.isQueryBoundP_bind (deriveRandomizer_queryBound _ _ _ _ _) ?_
      intro randomness _
      refine OracleComp.isQueryBoundP_bind (precomputedSignAttempt_queryBound _ _ _ _) ?_
      intro answer _
      cases answer with
      | none => exact ih _
      | some signature => exact OracleComp.isQueryBoundP_pure _ _ _

theorem xmss_sign_queryBound (secretKey : Generic.Seeded.SecretKey) (leafIndex : LeafIndex) (message : Message) :
    (Generic.xmss.sign secretKey leafIndex message).IsQueryBoundP IsHashQuery (signingAttemptLimit * 2) := by
  change (liftComp (Generic.Seeded.sign secretKey leafIndex message : OracleComp HashSpec (Option Generic.Signature))
    OracleWorld).IsQueryBoundP _ _
  exact OracleComp.IsQueryBoundP.liftComp_subSpec (p := fun _ => True) (q := IsHashQuery)
    (fun input => by change True ↔ IsHashQuery (.inr input); simp [IsHashQuery])
    (seededSignFrom_queryBound secretKey leafIndex message signingAttemptLimit 0)

theorem seededKeygenQueryBudget_le : seededKeygenQueryBudget ≤ 2 ^ 42 := by
  norm_num [seededKeygenQueryBudget, treeHashQueryCount, treeHeight, lifetime, numChains, chainLength, winternitzBits]

def neighborEverythingBudget : ℕ := 2 ^ 126 + 2 ^ 123

theorem neighbor_total_budget_le :
    seededKeygenQueryBudget + (signingAttemptLimit * 2 + neighborDirectBudget) + Direct.verifierQueryBound + 1 ≤
      neighborEverythingBudget := by
  have hhashes : Code.verificationChainHashes = verificationChainHashes := rfl
  apply le_trans (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_right seededKeygenQueryBudget_le _) _) _) ?_
  norm_num [neighborEverythingBudget, neighborDirectBudget, neighborSearchSteps, preimageSearchSteps,
    signingAttemptLimit, Direct.verifierQueryBound, hhashes, verificationChainHashes, treeHeight,
    numChains, chainLength, winternitzBits, targetSum]

theorem neighborEverythingBudget_ratio :
    (neighborEverythingBudget : ℝ≥0∞) / ((2 ^ 128 : ℕ) : ℝ≥0∞) = 9 / 32 := by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [neighborEverythingBudget, ENNReal.toReal_div]

/-- info: 'Xmss.TargetSum.Attack.xmss_keygen_queryBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_keygen_queryBound

/-- info: 'Xmss.TargetSum.Attack.xmss_sign_queryBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_sign_queryBound

end Xmss.TargetSum.Attack
