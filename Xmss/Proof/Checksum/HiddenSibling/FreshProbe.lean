import Xmss.Proof.Checksum.HiddenSibling.FreshPath
import Xmss.Proof.Checksum.Code
import Xmss.Proof.Generic.Direct.OptionalProbe

/-! A fresh checksum digest selects a changed, still hidden message-chain coordinate. -/

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational
open Xmss.Generic

set_option backward.isDefEq.respectTransparency false

namespace Xmss.Checksum.HiddenSibling

open Generic.Deciding Generic.CappedExecution Generic.FirstLaneOracleSimulation

noncomputable def referenceDigest (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (log : QueryLog SigningSpec) (leaf : LeafIndex) : Digest :=
  match returnedAt log leaf with
  | none => 0
  | some (request, signature) =>
      CacheView.encodingHash cache parameter leaf (request.message, signature.randomness)

def freshChain (signed digest : Digest) : Generic.ChainIndex :=
  Checksum.messageChain (firstMessageDifference (messageDigit signed) (messageDigit digest))

theorem referenceDigest_eq_of_comparableCaches (leftCache rightCache : QueryCache HashSpec)
    (parameter : PublicParameter)
    (hcaches : HashCachesAgreeOn (GlobalSigningComparableHashInput parameter) leftCache rightCache)
    (log : QueryLog SigningSpec) (leaf : LeafIndex) :
    referenceDigest leftCache parameter log leaf = referenceDigest rightCache parameter log leaf := by
  unfold referenceDigest
  cases returnedAt log leaf with
  | none => rfl
  | some pair =>
      rcases pair with ⟨request, signature⟩
      dsimp only
      unfold CacheView.encodingHash CacheView.digestAt
      rw [hcaches _ ⟨leaf, request.message, signature.randomness, rfl⟩]

theorem freshChain_not_sent (cache : QueryCache HashSpec) (secretKey : Generic.SecretKey)
    (log : QueryLog SigningSpec) (leaf : LeafIndex) (digest : Digest)
    (hvalid : SigningTranscript.Valid log)
    (hne : digest ≠ referenceDigest cache secretKey.parameter log leaf) :
    (freshChain (referenceDigest cache secretKey.parameter log leaf) digest, leaf,
      encode digest (freshChain (referenceDigest cache secretKey.parameter log leaf) digest)) ∉
        GlobalSentChainValueCovered cache secretKey log := by
  rintro ⟨request, signature, encoding, hreturned, hdecode, hepoch, hdigit⟩
  cases hselected : returnedAt log leaf with
  | none =>
      exact no_returned_of_returnedAt_none log leaf hselected
        ⟨request, signature, hreturned, hepoch.symm⟩
  | some pair =>
      obtain ⟨hselectedReturned, hselectedEpoch⟩ := returned_of_returnedAt log leaf pair.1 pair.2
        hselected
      obtain ⟨hrequest, hsignature⟩ := SigningTranscript.returned_eq_of_same_leafIndex hvalid
        hreturned hselectedReturned (hepoch.symm.trans hselectedEpoch.symm)
      have hencoding : encoding = encode (referenceDigest cache secretKey.parameter log leaf) := by
        unfold referenceDigest
        rw [hselected]
        rw [hrequest, hsignature, hselectedEpoch] at hdecode
        have hdecode := CacheView.decodeDigest_of_decodedEncoding hdecode
        change some (encode (CacheView.encodingHash cache secretKey.parameter leaf
          (pair.1.message, pair.2.randomness))) = some encoding at hdecode
        exact (Option.some.inj hdecode).symm
      rw [hencoding] at hdigit
      exact encode_firstMessageDifference_ne _ _ hne.symm hdigit.symm

def FreshSigned (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (log : QueryLog SigningSpec) (forgery : Generic.Forgery) : Prop :=
  cache (CacheView.encodingInput parameter forgery.epoch
    (forgery.message, forgery.signature.randomness)) = none ∧
    log ≠ [] ∧ SigningTranscript.Valid log

open Classical in
noncomputable def freshProbeFrom (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (log : QueryLog SigningSpec) (forgery : Generic.Forgery) (digest : Digest) : ProbeChoice :=
  let signed := referenceDigest cache parameter log forgery.epoch
  if FreshSigned cache parameter log forgery ∧ digest ≠ signed then
    let chain := freshChain signed digest
    some ((chain, forgery.epoch, encode digest chain), forgery.signature.chainValue chain)
  else none

noncomputable def freshProbeChoice (key : ProgrammedGlobalChainKeygenView)
    (result : Generic.Forgery × GlobalDirectTracedState) (digest : Digest) : ProbeChoice :=
  freshProbeFrom result.2.causalState.cache key.secretKey.parameter
    result.2.attackerTrace.toSigningLog result.1 digest

theorem freshProbeFrom_eq_of_comparableCaches (leftCache rightCache : QueryCache HashSpec)
    (parameter : PublicParameter)
    (hcaches : HashCachesAgreeOn (GlobalSigningComparableHashInput parameter) leftCache rightCache)
    (log : QueryLog SigningSpec) (forgery : Generic.Forgery) (digest : Digest) :
    freshProbeFrom leftCache parameter log forgery digest =
      freshProbeFrom rightCache parameter log forgery digest := by
  unfold freshProbeFrom FreshSigned
  rw [referenceDigest_eq_of_comparableCaches _ _ _ hcaches,
    hcaches _ ⟨forgery.epoch, forgery.message, forgery.signature.randomness, rfl⟩]

def FreshSourcePrefix (before : SourcePrefixResult) : Prop :=
  FreshSigned before.2.2.1.1.1 before.1.secretKey.parameter before.2.2.2.toSigningLog before.2.1

def SourceFreshSigned (sample : SourcePrefixResult × Digest) : Prop :=
  FreshSourcePrefix sample.1

def SourceFreshGuess (sample : SourcePrefixResult × Digest) : Prop :=
  let cache := sample.1.2.2.1.1.1
  let log := sample.1.2.2.2.toSigningLog
  let forgery := sample.1.2.1
  let signed := referenceDigest cache sample.1.1.secretKey.parameter log forgery.epoch
  let chain := freshChain signed sample.2
  SourceFreshSigned sample ∧ sample.2 ≠ signed ∧
    sample.1.1.table (chain, forgery.epoch, encode sample.2 chain) = forgery.signature.chainValue chain

theorem freshProbeChoice_eq_of_relation (left : SourcePrefixResult) (right : CoupledPrefixResult)
    (hrel : ZeroHashPrefixRelation left right) (digest : Digest) :
    freshProbeChoice right.1.1 right.2.1 digest =
      freshProbeFrom left.2.2.1.1.1 left.1.secretKey.parameter left.2.2.2.toSigningLog
        left.2.1 digest := by
  have hparameter := programmedGlobal_secretKey_parameter_eq left.1 right.1 hrel.keys
    hrel.source_key hrel.public_key
  have htrace : left.2.2.2 = right.2.1.2.attackerTrace := hrel.state.1.2
  obtain ⟨_, _, _, _, hcausal, _⟩ := hrel.state.1.1
  change GlobalFilteredCausalStateRelation left.1 right.1 left.2.2.1.1.1
    right.2.1.2.causalState at hcausal
  unfold freshProbeChoice
  rw [hparameter, htrace, hrel.forgery]
  exact (freshProbeFrom_eq_of_comparableCaches _ _ _ hcausal.1 _ _ _).symm

theorem sourceFreshGuess_implies_probeHit (adversary : Generic.Adversary)
    (hzero : Direct.IsDirectQueryBound adversary 0)
    (left : SourcePrefixResult × Digest) (right : CoupledPrefixResult × Digest)
    (hright : right ∈ support (sampledPrefixProgram (publicPrefixExecution adversary)))
    (hrel : ZeroHashPrefixRelation left.1 right.1) (hdigest : left.2 = right.2)
    (hguess : SourceFreshGuess left) : SampledProbeHit freshProbeChoice right := by
  classical
  let signed := referenceDigest left.1.2.2.1.1.1 left.1.1.secretKey.parameter
    left.1.2.2.2.toSigningLog left.1.2.1.epoch
  let chain := freshChain signed left.2
  let index : GlobalChainValueIndex := (chain, left.1.2.1.epoch, encode left.2 chain)
  obtain ⟨hfresh, hne, hvalue⟩ := hguess
  refine ⟨index, left.1.2.1.signature.chainValue chain, ?_, ?_, ?_⟩
  · rw [freshProbeChoice_eq_of_relation _ _ hrel, ← hdigest]
    exact if_pos ⟨hfresh, hne⟩
  · have htables : left.1.1.table = right.1.1.2 := hrel.keys.1.toStable.1.1
    rw [← htables]
    exact hvalue
  · intro value hreveal
    have hbefore := sampledPrefixProgram_support_prefix _ right hright
    have hbody := coupledFirstLaneProgram_support_body _ right.1 hbefore
    have hcovered := globalFirstLaneAdversary_zeroHash_support_sentCovered right.1.1.1
      right.1.1.2 (adversary.main right.1.1.1.publicKey) (hzero _)
      right.1.2 hbody
    have hsent := hcovered index value ((chainAction_mem_iff _ _).mpr hreveal)
    have hparameter := programmedGlobal_secretKey_parameter_eq left.1.1 right.1.1 hrel.keys
      hrel.source_key hrel.public_key
    have htrace : left.1.2.2.2 = right.1.2.1.2.attackerTrace := hrel.state.1.2
    obtain ⟨_, _, _, _, hcausal, _⟩ := hrel.state.1.1
    change GlobalFilteredCausalStateRelation left.1.1 right.1.1 left.1.2.2.1.1.1
      right.1.2.1.2.causalState at hcausal
    have hsentSource := globalSentChainValueCovered_of_comparableCaches
      left.1.1.secretKey.parameter left.1.2.2.1.1.1 right.1.2.1.2.causalState.cache
      left.1.1.secretKey right.1.1.1.secretKey left.1.2.2.2.toSigningLog
      right.1.2.1.2.attackerTrace.toSigningLog rfl hparameter
      (congrArg AttackerActionTrace.toSigningLog htrace.symm) hcausal.1 index hsent
    exact freshChain_not_sent _ _ _ _ _ hfresh.2.2 hne hsentSource

theorem sourceFreshGuess_probability_le (adversary : Generic.Adversary)
    (hzero : Direct.IsDirectQueryBound adversary 0) :
    Pr[SourceFreshGuess | sourceSampledPrefixProgram adversary] ≤
      ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ *
        Pr[SourceFreshSigned | sourceSampledPrefixProgram adversary] := by
  classical
  refine (zeroHash_sampled_probe_probability_le adversary hzero freshProbeChoice SourceFreshGuess
    (sourceFreshGuess_implies_probeHit adversary hzero)).trans ?_
  apply mul_le_mul' le_rfl
  apply probEvent_le_of_relTriple (relTriple_symm (zeroHash_sampled_prefix_coupling adversary hzero))
  intro right left hrel hsome
  rw [freshProbeChoice_eq_of_relation _ _ hrel.1, ← hrel.2] at hsome
  unfold freshProbeFrom at hsome
  dsimp only at hsome
  split at hsome
  · rename_i hguard
    exact hguard.1
  · simp at hsome

end Xmss.Checksum.HiddenSibling
