import Xmss.Proof.TargetSum.AcceptedEventCoupling
import Xmss.Proof.TargetSum.Direct.SourcePrefixAcceptance
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! Transfer the winning and acceptance events through the same limited-prefix
coupling. Collisions on rejected source prefixes cancel their extra probe charge. -/

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum.Deciding

open CappedExecution FirstLaneOracleSimulation

def SourceCountedPrefixFirstLane (result : CappedExecution.ProgrammedGlobalChainKeygenView × (Forgery × CountedSourceState)) : Prop :=
  AcceptedPrefixFirstLaneEvent result.1 (result.2.1, result.2.2.toSource)

def CoupledLimitedProbedHit (result : CoupledLimitedPrefixResult) : Prop :=
  FirstLaneOracleSimulation.CombinedHit result.1.2 (appendLimitedAcceptedPrefixProbe result.1.2 result.1.1 result.2).2

theorem acceptedPrefixFirstLane_implies_accepted (key : CappedExecution.ProgrammedGlobalChainKeygenView)
    (result : Forgery × CountedSourceState)
    (hevent : AcceptedPrefixFirstLaneEvent key (result.1, result.2.toSource)) :
    HasAcceptedEncoding key.secretKey.parameter result.2.counts.cache := by
  obtain ⟨encoding, hencoding⟩ := Option.isSome_iff_exists.mp hevent.2
  exact hasAcceptedEncoding_of_decode _ _ _ _ _ _ hencoding

theorem sourceCountedPrefixProgram_source_projection (adversary : Adversary) :
    (fun result : CappedExecution.ProgrammedGlobalChainKeygenView × (Forgery × CountedSourceState) =>
      (result.1, (result.2.1, result.2.2.toSource))) <$> sourceCountedPrefixProgram adversary =
        Deciding.sourcePrefixProgram adversary := by
  unfold sourceCountedPrefixProgram Deciding.sourcePrefixProgram
  simp only [map_bind, bind_pure_comp]
  apply bind_congr
  intro key
  rw [← comp_map]
  change (fun result : Forgery × CountedSourceState => (key, (result.1, result.2.toSource))) <$>
    sourceCountedPrefixExecution adversary key = _
  rw [show (fun result : Forgery × CountedSourceState => (key, (result.1, result.2.toSource))) =
    (fun result => (key, result)) ∘ Prod.map id CountedSourceState.toSource from rfl, comp_map]
  unfold sourceCountedPrefixExecution
  rw [countedSource_source_projection key.publicKey]
  rfl

end Xmss.TargetSum.Deciding
