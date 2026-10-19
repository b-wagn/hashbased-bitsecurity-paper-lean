import XmssSecurity.Proof.Generic.Direct.DecidingPrefixBound
import XmssSecurity.Proof.Generic.Direct.ZeroHashCoverage

/-! The source and public prefix experiments couple exactly when the adversary makes no hash
queries. There is no first-lane loss before appending the verifier's encoding and chain probe. -/

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.Generic.Deciding

variable [Code]

open CappedChain FirstLaneOracleSimulation

abbrev SourcePrefixResult := ProgrammedGlobalChainKeygenView × (Forgery × SourceExactTracedState)

abbrev CoupledPrefixResult :=
  BaseKey × ((Forgery × GlobalDirectTracedState) × ActionTrace GlobalChainValueIndex)

structure ZeroHashPrefixRelation (left : SourcePrefixResult) (right : CoupledPrefixResult) : Prop where
  keys : ProgrammedGlobalChainKeygenBaseStableRelation left.1 right.1
  source_key : left.1 ∈ support trajectoryProgrammedGlobalChainKeygen
  public_key : right.1.1 ∈ support trajectoryProgrammedGlobalChainKeygen
  forgery : left.2.1 = right.2.1.1
  state : SourceFirstLaneExactGoodStateRelation left.1 right.1 left.2.2 right.2.1.2 right.2.2
  hazards : hazardCount right.2.2 = 0

theorem zeroHash_prefix_coupling_or_hit (adversary : Adversary)
    (hzero : Direct.IsDirectQueryBound adversary 0) :
    RelTriple (sourcePrefixProgram adversary)
      (coupledFirstLaneProgram (publicPrefixExecution adversary))
      (fun left right => ZeroHashPrefixRelation left right ∨
        CombinedHit right.1.2 (enforceHazardTrace 0 right.2.2)) := by
  unfold sourcePrefixProgram coupledFirstLaneProgram
  apply relTriple_bind (relTriple_with_support
    relTriple_trajectoryProgrammedGlobalChainKeygen_withBase_stable)
  intro left right hkeys
  obtain ⟨hkey, hleft, hright⟩ := hkeys
  have hrightKey := coupledGlobalChainKeygenWithBaseFull_support_keyView right hright
  have hpk : left.publicKey = right.1.publicKey := hkey.1.toStable.1.2.1
  have hprefix := relTriple_sourceExact_firstLane_adversary_boundedHit_direct 0 0 le_rfl
    adversary left right hkey hleft hrightKey (hzero left.publicKey)
  have hprefix' : RelTriple (sourcePrefixExecution adversary left)
      ((simulateQ (eagerTraceImpl right.2) (publicPrefixExecution adversary right.1)).run)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1.1 ∧
          SourceFirstLaneExactGoodStateRelation left right leftResult.2 rightResult.1.2
            rightResult.2 ∧ hazardCount rightResult.2 ≤ 0) ∨
          CombinedHit right.2 (enforceHazardTrace 0 rightResult.2)) := by
    simpa only [sourcePrefixExecution, publicPrefixExecution, hpk] using hprefix
  apply relTriple_bind hprefix'
  intro leftResult rightResult hresult
  apply relTriple_pure_pure
  rcases hresult with ⟨hforgery, hstate, hcount⟩ | hhit
  · exact Or.inl ⟨hkey, hleft, hrightKey, hforgery, hstate, Nat.eq_zero_of_le_zero hcount⟩
  · exact Or.inr hhit

/-- No additive guessing loss is required for the hash-free adversary prefix. -/
theorem zeroHash_prefix_coupling (adversary : Adversary)
    (hzero : Direct.IsDirectQueryBound adversary 0) :
    RelTriple (sourcePrefixProgram adversary)
      (coupledFirstLaneProgram (publicPrefixExecution adversary)) ZeroHashPrefixRelation := by
  have hzeroHit : Pr[fun result : CoupledPrefixResult =>
      CombinedHit result.1.2 (enforceHazardTrace 0 result.2.2) |
      coupledFirstLaneProgram (publicPrefixExecution adversary)] = 0 := by
    apply le_antisymm _ zero_le
    simpa using coupled_enforcedHit_probability_le 0 (publicPrefixExecution adversary)
  apply relTriple_post_mono (relTriple_with_support (zeroHash_prefix_coupling_or_hit adversary hzero))
  intro left right hrel
  rcases hrel.1 with hgood | hhit
  · exact hgood
  · exact (probEvent_eq_zero_iff.mp hzeroHit right hrel.2.2 hhit).elim

end XmssSecurity.Generic.Deciding
