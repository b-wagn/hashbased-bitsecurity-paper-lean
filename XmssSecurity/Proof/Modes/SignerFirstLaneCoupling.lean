import XmssSecurity.Proof.Modes.SignerSourceBudget
import XmssSecurity.Proof.Direct.CountedPrefixCoupling
import XmssSecurity.Proof.Direct.FirstLaneSampleBudget

/-! The statement's signer budget reaches the complete first-lane prefix coupling.
On its good branch, direct hazards and the actual source signer cost share that budget. -/

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.Modes

open Seeded DeterministicSigning CappedChain FirstLaneOracleSimulation

theorem signer_firstLane_prefix_coupling
    (adversary : Security.StatementAdversary) (q : Nat) (hsmall : q < 2 ^ 256)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound xmss adversary q)
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView × (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support trajectoryProgrammedGlobalChainKeygen) :
    RelTriple
      ((simulateQ (countedSourceImpl (Concrete.materializePrecomputation left.cache left.secretKey))
        (memoize (adversary.main left.publicKey) ∅)).run (CountedSourceState.initial left.cache))
      ((simulateQ (eagerTraceImpl right.1.2)
        ((simulateQ (globalFirstLaneExactTracedMappedAdversaryImpl right.1.1 right.2)
          (memoize (adversary.main left.publicKey) ∅)).run
            (GlobalHighDirectTracedState.initial (globalFilteredCausalKeygenState right.1.1)))).run)
      (fun leftResult rightResult =>
        leftResult.2.charge ≤ q ∧
        ((leftResult.1 = rightResult.1.1 ∧
          SourceFirstLaneExactGoodStateRelation left right.1 leftResult.2.toSource
            rightResult.1.2 rightResult.2 ∧
          hazardCount rightResult.2 ≤ leftResult.2.counts.direct ∧
          hazardCount rightResult.2 + 2 * leftResult.2.counts.signing ≤ q) ∨
          CombinedHit right.1.2 (enforceHazardTrace q rightResult.2))) := by
  have hbudget := signer_countedSourceBudget_after_trajectory adversary q hsmall hbound
    left hleftSupport
  apply relTriple_post_mono (relTriple_countedSource_firstLane_prefix q q le_rfl left right
    hrel hleftSupport hrightSupport (memoize (adversary.main left.publicKey) ∅) hbudget)
  intro leftResult rightResult hresult
  refine ⟨hresult.1, ?_⟩
  rcases hresult.2 with hgood | hhit
  · exact Or.inl ⟨hgood.1, hgood.2.1, hgood.2.2,
      (Nat.add_le_add_right hgood.2.2 _).trans hresult.1⟩
  · exact Or.inr hhit

theorem signer_firstLane_observableBudget_coupling
    (adversary : Security.StatementAdversary) (q : Nat) (hsmall : q < 2 ^ 256)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound xmss adversary q)
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView × (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support trajectoryProgrammedGlobalChainKeygen) :
    RelTriple
      ((simulateQ (countedSourceImpl (Concrete.materializePrecomputation left.cache left.secretKey))
        (memoize (adversary.main left.publicKey) ∅)).run (CountedSourceState.initial left.cache))
      ((simulateQ (eagerTraceImpl right.1.2)
        ((simulateQ (globalFirstLaneExactTracedMappedAdversaryImpl right.1.1 right.2)
          (memoize (adversary.main left.publicKey) ∅)).run
            (GlobalHighDirectTracedState.initial (globalFilteredCausalKeygenState right.1.1)))).run)
      (fun leftResult rightResult =>
        leftResult.2.charge ≤ q ∧
        ((leftResult.1 = rightResult.1.1 ∧
          SourceFirstLaneExactGoodStateRelation left right.1 leftResult.2.toSource
            rightResult.1.2 rightResult.2 ∧
          observableFirstLaneCharge right.1.1.secretKey.parameter rightResult.1.2 rightResult.2 ≤ q) ∨
          CombinedHit right.1.2 (enforceHazardTrace q rightResult.2))) := by
  apply relTriple_post_mono (relTriple_with_support
    (signer_firstLane_prefix_coupling adversary q hsmall hbound left right hrel hleftSupport hrightSupport))
  intro leftResult rightResult hresult
  obtain ⟨⟨hcharge, hcases⟩, hleft, hright⟩ := hresult
  refine ⟨hcharge, ?_⟩
  rcases hcases with hgood | hhit
  · refine Or.inl ⟨hgood.1, hgood.2.1, ?_⟩
    exact (countedSource_firstLane_observableCharge_le left right hrel hleftSupport hrightSupport
      (memoize (adversary.main left.publicKey) ∅) leftResult rightResult hleft hright hgood.2.1
      hgood.2.2.1).trans hcharge
  · exact Or.inr hhit

/-- info: 'XmssSecurity.Modes.signer_firstLane_prefix_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signer_firstLane_prefix_coupling

/-- info: 'XmssSecurity.Modes.signer_firstLane_observableBudget_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signer_firstLane_observableBudget_coupling

end XmssSecurity.Modes
