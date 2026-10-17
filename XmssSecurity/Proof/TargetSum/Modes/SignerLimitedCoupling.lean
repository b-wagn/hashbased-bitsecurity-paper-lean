import XmssSecurity.Proof.TargetSum.Modes.SignerSourceBudget
import XmssSecurity.Proof.TargetSum.Direct.LimitedPrefixCoupling
import XmssSecurity.Proof.TargetSum.Direct.LimitedFirstLaneExpected

/-! The unchanged signer-mode query bound controls both sides of the coupling to
the limited public first-lane experiment, including all post-collision executions. -/

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Modes
open XmssSecurity.Modes

open Seeded DeterministicSigning CappedChain FirstLaneOracleSimulation

theorem signer_limitedFirstLane_prefix_coupling
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
        (limitedFirstLanePrefix q right.1.1 right.2 (memoize (adversary.main left.publicKey) ∅)
          (GlobalHighDirectTracedState.initial (globalFilteredCausalKeygenState right.1.1)) ⟨0, 0, 0⟩)).run)
      (fun source target => source.2.charge ≤ q ∧ target.1.2.charge ≤ q ∧
        target.1.2.samples = target.2.encodingActions.length ∧
        hazardCount target.2 ≤ target.1.2.direct ∧
        LimitedFirstLaneOutcomeRelation left right.1 [] source target) :=
  relTriple_countedSource_limitedPrefix left right hrel hleftSupport hrightSupport q
    (memoize (adversary.main left.publicKey) ∅)
    (signer_countedSourceBudget_after_trajectory adversary q hsmall hbound left hleftSupport)

theorem signer_acceptedPrefixFirstLane_probability_le_limited_expected
    (adversary : Security.StatementAdversary) (q : Nat) (hsmall : q < 2 ^ 256)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound xmss adversary q) :
    Pr[fun result => Deciding.AcceptedPrefixFirstLaneEvent result.1 result.2 |
      Deciding.sourcePrefixProgram (memoAdversary (Security.embed adversary))] ≤
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ * Deciding.expectedCoupledHazards (q + 1)
        (Deciding.publicLimitedAcceptedPrefixProbeExecution q (memoAdversary (Security.embed adversary))) :=
  Deciding.acceptedPrefixFirstLane_probability_le_limited_expected (memoAdversary (Security.embed adversary)) q
    (signer_countedSourceBudget_after_trajectory adversary q hsmall hbound)

/-- info: 'XmssSecurity.TargetSum.Modes.signer_limitedFirstLane_prefix_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signer_limitedFirstLane_prefix_coupling

/-- info: 'XmssSecurity.TargetSum.Modes.signer_acceptedPrefixFirstLane_probability_le_limited_expected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signer_acceptedPrefixFirstLane_probability_le_limited_expected

end XmssSecurity.TargetSum.Modes
