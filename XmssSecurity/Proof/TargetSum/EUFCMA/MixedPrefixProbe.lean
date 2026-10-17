import XmssSecurity.Proof.TargetSum.EUFCMA.FreshFirstLane
import XmssSecurity.Proof.TargetSum.Direct.MixedFirstLane

/-! Cached and independently supplied encodings use one shared adversary prefix
and one deciding probe. A direct-query bound suffices for this experiment. -/

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.EUFCMA
open XmssSecurity.EUFCMA

open Concrete CappedChain Deciding FirstLaneOracleSimulation

noncomputable def mixedPrefixEncoding (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (forgery : Forgery) (fallback : Option Encoding) : Encoding :=
  (mixedProbeEncoding cache parameter forgery fallback).getD (fun _ => ⟨0, by decide⟩)

noncomputable def publicMixedPrefixProbeExecution (adversary : XmssSecurity.TargetSum.Adversary)
    (fallback : Option Encoding) (key : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    OracleComp GlobalFirstLaneWorld (Forgery × GlobalHighDirectTracedState) := do
  let result ← publicPrefixExecution adversary key edgeHigh
  let _ ← publicDecidingProbe result.1.epoch
    (signedEncoding result.2.causalState.cache key.secretKey.parameter
      result.2.attackerTrace.toSigningLog result.1.epoch)
    (mixedPrefixEncoding result.2.causalState.cache key.secretKey.parameter result.1 fallback)
    result.1.signature.chainValue
  pure result

noncomputable def appendMixedPrefixProbe (base : GlobalChainValueIndex → Digest)
    (key : ProgrammedGlobalChainKeygenView) (fallback : Option Encoding)
    (result : (Forgery × GlobalHighDirectTracedState) × ActionTrace GlobalChainValueIndex) :
    (Forgery × GlobalHighDirectTracedState) × ActionTrace GlobalChainValueIndex :=
  (result.1, result.2 ++ (decidingProbeResult base result.1.1.epoch
    (signedEncoding result.1.2.causalState.cache key.secretKey.parameter
      result.1.2.attackerTrace.toSigningLog result.1.1.epoch)
    (mixedPrefixEncoding result.1.2.causalState.cache key.secretKey.parameter result.1.1 fallback)
    result.1.1.signature.chainValue).2)

theorem publicMixedPrefixProbeExecution_eager (adversary : XmssSecurity.TargetSum.Adversary) (fallback : Option Encoding)
    (key : ProgrammedGlobalChainKeygenView) (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    (simulateQ (eagerTraceImpl base) (publicMixedPrefixProbeExecution adversary fallback key edgeHigh)).run =
      appendMixedPrefixProbe base key fallback <$>
        (simulateQ (eagerTraceImpl base) (publicPrefixExecution adversary key edgeHigh)).run := by
  unfold publicMixedPrefixProbeExecution
  simp only [simulateQ_bind, WriterT.run_bind']
  apply bind_congr
  intro result
  rw [publicDecidingProbe_eager]
  simp [appendMixedPrefixProbe, Prod.map]
  rfl

theorem mixedPrefix_coupling_afterKeygen (adversary : XmssSecurity.TargetSum.Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D) (fallback : Option Encoding)
    (left : ProgrammedGlobalChainKeygenView) (right : BaseHighKey)
    (hkey : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleft : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hright : right.1.1 ∈ support trajectoryProgrammedGlobalChainKeygen) :
    RelTriple (sourcePrefixExecution adversary left)
      ((simulateQ (eagerTraceImpl right.1.2)
        (publicMixedPrefixProbeExecution adversary fallback right.1.1 right.2)).run)
      (fun source target => MixedEncodingPrefixEvent left source fallback →
        CombinedHit right.1.2 (enforceHazardTrace (D + 1) target.2)) := by
  rw [publicMixedPrefixProbeExecution_eager]
  have hpk : left.publicKey = right.1.1.publicKey := hkey.1.toStable.1.2.1
  have hcoupling := relTriple_sourceExact_firstLane_adversary_boundedHit_direct D (D + 1)
    (by omega) adversary left right hkey hleft hright (hD left.publicKey)
  have hrightProgram : (simulateQ (eagerTraceImpl right.1.2)
      (publicPrefixExecution adversary right.1.1 right.2)).run =
    (simulateQ (eagerTraceImpl right.1.2)
      ((simulateQ (globalFirstLaneExactTracedMappedAdversaryImpl right.1.1 right.2)
        (adversary.main left.publicKey)).run
          (GlobalHighDirectTracedState.initial (globalFilteredCausalKeygenState right.1.1)))).run := by
    unfold publicPrefixExecution
    rw [hpk]
  rw [hrightProgram, ← id_map (sourcePrefixExecution adversary left)]
  apply relTriple_map
  apply relTriple_post_mono (relTriple_with_support hcoupling)
  intro source target hresult hevent
  change MixedEncodingPrefixEvent left source fallback at hevent
  obtain ⟨hrel, _hsource, htarget⟩ := hresult
  rcases hrel with ⟨hforgery, hgood, hcount⟩ | hhit
  · rw [hpk] at htarget
    have hcovered := globalFirstLaneAdversary_support_returnedCovered right.1.1 right.1.2
      right.2 (adversary.main right.1.1.publicKey) target htarget
    have hparameter := programmedGlobal_secretKey_parameter_eq left right hkey hleft hright
    obtain ⟨_monitor, _hmonitor, _hagrees, _hrevealed, hcausal, _hretained⟩ := hgood.1.1
    have hencoding : forgedEncoding source.2.1.1.1 left.secretKey.parameter source.1 =
        forgedEncoding target.1.2.causalState.cache right.1.1.secretKey.parameter target.1.1 := by
      rw [hparameter, ← hforgery]
      exact forgedEncoding_eq_of_comparableCaches _ _ _ hcausal.1 _
    rw [enforceHazardTrace_eq_self_of_count_le]
    · rcases hevent with hcached | ⟨hnone, encoding, hfallback, hrevealed⟩
      · obtain ⟨encoding, hdecode⟩ := Option.isSome_iff_exists.mp hcached.2
        rw [hencoding] at hdecode
        have hhit := prefixFirstLaneEvent_good_implies_hit left right hkey hleft hright
          source target hforgery hgood hcovered hcached.1
        simpa only [appendMixedPrefixProbe, mixedPrefixEncoding, mixedProbeEncoding,
          prefixProbeResult, prefixProbeEncoding, hdecode, Option.orElse_some, Option.getD_some] using hhit
      · rw [hencoding] at hnone
        simpa only [appendMixedPrefixProbe, mixedPrefixEncoding, mixedProbeEncoding, hnone,
          Option.orElse_none, hfallback, Option.getD_some] using
            revealedEncodingPrefixEvent_good_implies_hit left right hkey hleft hright
              source target hforgery hgood hcovered encoding hrevealed
    · simpa only [appendMixedPrefixProbe, hazardCount_append, decidingProbeResult_hazardCount] using
        Nat.add_le_add_right hcount 1
  · exact CombinedHit.enforce_append_of_prefix _ _ _ _ hhit

theorem mixedPrefix_coupling (adversary : XmssSecurity.TargetSum.Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D) (fallback : Option Encoding) :
    RelTriple (sourcePrefixProgram adversary)
      (coupledFirstLaneProgram (publicMixedPrefixProbeExecution adversary fallback))
      (fun source target => MixedEncodingPrefixEvent source.1 source.2 fallback →
        CombinedHit target.1.1.2 (enforceHazardTrace (D + 1) target.2.2)) := by
  unfold sourcePrefixProgram coupledFirstLaneProgram
  apply relTriple_bind (relTriple_with_support
    relTriple_trajectoryProgrammedGlobalChainKeygen_withBaseHigh_stable)
  intro left right hkeys
  obtain ⟨hkey, hleft, hright⟩ := hkeys
  apply relTriple_bind (mixedPrefix_coupling_afterKeygen adversary D hD fallback left right hkey hleft
    (coupledGlobalChainKeygenWithBaseHighFull_support_keyView right hright))
  intro source target hresult
  exact relTriple_pure_pure hresult

theorem mixedPrefix_probability_le_direct (adversary : XmssSecurity.TargetSum.Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D) (fallback : Option Encoding) :
    Pr[fun result => MixedEncodingPrefixEvent result.1 result.2 fallback | sourcePrefixProgram adversary] ≤
      ((D + 1 : ℕ) : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
  apply le_trans _ (coupled_enforcedHit_probability_le (D + 1) (publicMixedPrefixProbeExecution adversary fallback))
  apply probEvent_le_of_relTriple (mixedPrefix_coupling adversary D hD fallback)
  intro source target hrel hevent
  exact hrel hevent

/-- info: 'XmssSecurity.TargetSum.EUFCMA.mixedPrefix_probability_le_direct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mixedPrefix_probability_le_direct

end XmssSecurity.TargetSum.EUFCMA
