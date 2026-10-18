import XmssSecurity.Proof.TargetSum.EUFCMA.FreshFirstLane
import XmssSecurity.Proof.TargetSum.Direct.MixedFirstLane
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Cached and independently supplied encodings use one shared adversary prefix
and one deciding probe. A direct-query bound suffices for this experiment. -/

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.EUFCMA
open XmssSecurity.EUFCMA

open Concrete CappedChain Deciding FirstLaneOracleSimulation

noncomputable def mixedPrefixEncoding (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (forgery : Forgery) (fallback : Option Encoding) : Encoding :=
  (mixedProbeEncoding cache parameter forgery fallback).getD (fun _ => ⟨0, by decide⟩)

noncomputable def publicMixedPrefixProbeExecution (adversary : Adversary)
    (fallback : Option Encoding) (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (edgeHigh : CappedChain.GlobalChainEdgeIndex → Digest) :
    OracleComp CappedChain.GlobalFirstLaneWorld (Forgery × CappedChain.GlobalHighDirectTracedState) := do
  let result ← Deciding.publicPrefixExecution adversary key edgeHigh
  let _ ← Deciding.publicDecidingProbe result.1.epoch
    (Deciding.signedEncoding result.2.causalState.cache key.secretKey.parameter
      result.2.attackerTrace.toSigningLog result.1.epoch)
    (mixedPrefixEncoding result.2.causalState.cache key.secretKey.parameter result.1 fallback)
    result.1.signature.chainValue
  pure result

noncomputable def appendMixedPrefixProbe (base : CappedChain.GlobalChainValueIndex → Digest)
    (key : CappedChain.ProgrammedGlobalChainKeygenView) (fallback : Option Encoding)
    (result : (Forgery × CappedChain.GlobalHighDirectTracedState) × FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex) :
    (Forgery × CappedChain.GlobalHighDirectTracedState) × FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex :=
  (result.1, result.2 ++ (Deciding.decidingProbeResult base result.1.1.epoch
    (Deciding.signedEncoding result.1.2.causalState.cache key.secretKey.parameter
      result.1.2.attackerTrace.toSigningLog result.1.1.epoch)
    (mixedPrefixEncoding result.1.2.causalState.cache key.secretKey.parameter result.1.1 fallback)
    result.1.1.signature.chainValue).2)

theorem publicMixedPrefixProbeExecution_eager (adversary : Adversary) (fallback : Option Encoding)
    (key : CappedChain.ProgrammedGlobalChainKeygenView) (base : CappedChain.GlobalChainValueIndex → Digest)
    (edgeHigh : CappedChain.GlobalChainEdgeIndex → Digest) :
    (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl base) (publicMixedPrefixProbeExecution adversary fallback key edgeHigh)).run =
      appendMixedPrefixProbe base key fallback <$>
        (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl base) (Deciding.publicPrefixExecution adversary key edgeHigh)).run := by
  unfold publicMixedPrefixProbeExecution
  simp only [simulateQ_bind, WriterT.run_bind']
  apply bind_congr
  intro result
  rw [Deciding.publicDecidingProbe_eager]
  simp [appendMixedPrefixProbe, Prod.map]
  rfl

theorem mixedPrefix_coupling_afterKeygen (adversary : Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D) (fallback : Option Encoding)
    (left : CappedChain.ProgrammedGlobalChainKeygenView) (right : Deciding.BaseHighKey)
    (hkey : CappedChain.ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleft : left ∈ support CappedChain.trajectoryProgrammedGlobalChainKeygen)
    (hright : right.1.1 ∈ support CappedChain.trajectoryProgrammedGlobalChainKeygen) :
    RelTriple (Deciding.sourcePrefixExecution adversary left)
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
        (publicMixedPrefixProbeExecution adversary fallback right.1.1 right.2)).run)
      (fun source target => MixedEncodingPrefixEvent left source fallback →
        FirstLaneOracleSimulation.CombinedHit right.1.2 (FirstLaneOracleSimulation.enforceHazardTrace (D + 1) target.2)) := by
  rw [publicMixedPrefixProbeExecution_eager]
  have hpk : left.publicKey = right.1.1.publicKey := hkey.1.toStable.1.2.1
  have hcoupling := CappedChain.relTriple_sourceExact_firstLane_adversary_boundedHit_direct D (D + 1)
    (by omega) adversary left right hkey hleft hright (hD left.publicKey)
  have hrightProgram : (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
      (Deciding.publicPrefixExecution adversary right.1.1 right.2)).run =
    (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
      ((simulateQ (CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl right.1.1 right.2)
        (adversary.main left.publicKey)).run
          (CappedChain.GlobalHighDirectTracedState.initial (CappedChain.globalFilteredCausalKeygenState right.1.1)))).run := by
    unfold Deciding.publicPrefixExecution
    rw [hpk]
  rw [hrightProgram, ← id_map (Deciding.sourcePrefixExecution adversary left)]
  apply relTriple_map
  apply relTriple_post_mono (relTriple_with_support hcoupling)
  intro source target hresult hevent
  change MixedEncodingPrefixEvent left source fallback at hevent
  obtain ⟨hrel, _hsource, htarget⟩ := hresult
  rcases hrel with ⟨hforgery, hgood, hcount⟩ | hhit
  · rw [hpk] at htarget
    have hcovered := CappedChain.globalFirstLaneAdversary_support_returnedCovered right.1.1 right.1.2
      right.2 (adversary.main right.1.1.publicKey) target htarget
    have hparameter := CappedChain.programmedGlobal_secretKey_parameter_eq left right hkey hleft hright
    obtain ⟨_monitor, _hmonitor, _hagrees, _hrevealed, hcausal, _hretained⟩ := hgood.1.1
    have hencoding : Deciding.forgedEncoding source.2.1.1.1 left.secretKey.parameter source.1 =
        Deciding.forgedEncoding target.1.2.causalState.cache right.1.1.secretKey.parameter target.1.1 := by
      rw [hparameter, ← hforgery]
      exact forgedEncoding_eq_of_comparableCaches _ _ _ hcausal.1 _
    rw [FirstLaneOracleSimulation.enforceHazardTrace_eq_self_of_count_le]
    · rcases hevent with hcached | ⟨hnone, encoding, hfallback, hrevealed⟩
      · obtain ⟨encoding, hdecode⟩ := Option.isSome_iff_exists.mp hcached.2
        rw [hencoding] at hdecode
        have hhit := Deciding.prefixFirstLaneEvent_good_implies_hit left right hkey hleft hright
          source target hforgery hgood hcovered hcached.1
        simpa only [appendMixedPrefixProbe, mixedPrefixEncoding, mixedProbeEncoding,
          Deciding.prefixProbeResult, Deciding.prefixProbeEncoding, hdecode, Option.orElse_some, Option.getD_some] using hhit
      · rw [hencoding] at hnone
        simpa only [appendMixedPrefixProbe, mixedPrefixEncoding, mixedProbeEncoding, hnone,
          Option.orElse_none, hfallback, Option.getD_some] using
            revealedEncodingPrefixEvent_good_implies_hit left right hkey hleft hright
              source target hforgery hgood hcovered encoding hrevealed
    · simpa only [appendMixedPrefixProbe, FirstLaneOracleSimulation.hazardCount_append, Deciding.decidingProbeResult_hazardCount] using
        Nat.add_le_add_right hcount 1
  · exact FirstLaneOracleSimulation.CombinedHit.enforce_append_of_prefix _ _ _ _ hhit

theorem mixedPrefix_coupling (adversary : Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D) (fallback : Option Encoding) :
    RelTriple (Deciding.sourcePrefixProgram adversary)
      (Deciding.coupledFirstLaneProgram (publicMixedPrefixProbeExecution adversary fallback))
      (fun source target => MixedEncodingPrefixEvent source.1 source.2 fallback →
        FirstLaneOracleSimulation.CombinedHit target.1.1.2 (FirstLaneOracleSimulation.enforceHazardTrace (D + 1) target.2.2)) := by
  unfold Deciding.sourcePrefixProgram Deciding.coupledFirstLaneProgram
  apply relTriple_bind (relTriple_with_support
    CappedChain.relTriple_trajectoryProgrammedGlobalChainKeygen_withBaseHigh_stable)
  intro left right hkeys
  obtain ⟨hkey, hleft, hright⟩ := hkeys
  apply relTriple_bind (mixedPrefix_coupling_afterKeygen adversary D hD fallback left right hkey hleft
    (CappedChain.coupledGlobalChainKeygenWithBaseHighFull_support_keyView right hright))
  intro source target hresult
  exact relTriple_pure_pure hresult

theorem mixedPrefix_probability_le_direct (adversary : Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D) (fallback : Option Encoding) :
    Pr[fun result => MixedEncodingPrefixEvent result.1 result.2 fallback | Deciding.sourcePrefixProgram adversary] ≤
      ((D + 1 : ℕ) : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
  apply le_trans _ (Deciding.coupled_enforcedHit_probability_le (D + 1) (publicMixedPrefixProbeExecution adversary fallback))
  apply probEvent_le_of_relTriple (mixedPrefix_coupling adversary D hD fallback)
  intro source target hrel hevent
  exact hrel hevent

/-- info: 'XmssSecurity.TargetSum.EUFCMA.mixedPrefix_probability_le_direct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mixedPrefix_probability_le_direct

end XmssSecurity.TargetSum.EUFCMA
