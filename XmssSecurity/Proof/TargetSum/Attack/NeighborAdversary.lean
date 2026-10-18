import XmssSecurity.Proof.TargetSum.Attack.NeighborExperiment
import XmssSecurity.Proof.TargetSum.Attack.MutationGame
import XmssSecurity.Proof.Generic.Direct.SeedGuessing
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability
/-! The concrete one-request adversary using neighboring encodings and bounded predecessor search. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.Attack

open Concrete

def neighborRequest : SignRequest := Attack.mutationRequest

def neighborMessage : Message := 1

theorem neighborMessage_ne_request : neighborMessage ≠ neighborRequest.message := by decide

def neighborForgery (signature : Generic.Signature) : Forgery := ⟨neighborRequest.epoch, neighborMessage, signature⟩

noncomputable def neighborFinish (publicKey : PublicKey) (original : Generic.Signature) (encoding : Encoding)
    (randomness : Randomness) (transfer : DigitTransfer encoding) (block : PreimagePrefix) :
    OracleComp HashSpec Generic.Signature := do
  let answer ← findDigestPreimage (Concrete.CacheView.chainInput publicKey.parameter neighborRequest.epoch
    transfer.1.1 (predecessorStep encoding transfer.1)) (original.chainValue transfer.1.1) block
  match answer with
  | none => pure Attack.fallbackSignature
  | some (position, _) =>
      let advanced ← advanceSignatureChain publicKey.parameter neighborRequest.epoch original encoding transfer
      pure (transferredSignature original randomness encoding transfer (preimageCandidate block position) advanced)

noncomputable def neighborAfterEncoding (publicKey : PublicKey) (original : Generic.Signature)
    (encoding : Encoding) : OracleComp OracleWorld Generic.Signature := by
  classical
  exact do
    let answer ← liftM (findEncodingNeighbor publicKey.parameter neighborRequest.epoch neighborMessage encoding)
    match answer with
    | none => pure Attack.fallbackSignature
    | some (position, output) =>
        if hmem : Generic.truncateHash output ∈ neighborDigests encoding then
          let block ← worldPrivateSamples ($ᵗ PreimagePrefix)
          liftM (neighborFinish publicKey original encoding (BitVec.ofNat randomnessBits position)
            (selectedNeighborTransfer encoding (Generic.truncateHash output) hmem) block)
        else pure Attack.fallbackSignature

noncomputable def neighborAfterSigning (publicKey : PublicKey) : Option Generic.Signature → OracleComp OracleWorld Generic.Signature
  | none => pure Attack.fallbackSignature
  | some original => do
      let digest ← liftM (Generic.Concrete.encodingHash publicKey.parameter neighborRequest.epoch
        neighborRequest.message original.randomness : OracleComp HashSpec Digest)
      match Code.decodeDigest digest with
      | none => pure Attack.fallbackSignature
      | some encoding => neighborAfterEncoding publicKey original encoding

def liftWorldToAdversary {α : Type} (computation : OracleComp OracleWorld α) :
    OracleComp (OracleWorld + SigningSpec) α :=
  simulateQ (fun input => liftM ((OracleWorld + SigningSpec).query (.inl input))) computation

theorem liftWorldToAdversary_queryBound {α : Type} (computation : OracleComp OracleWorld α)
    (source : OracleWorld.Domain → Prop) [DecidablePred source]
    (target : (OracleWorld + SigningSpec).Domain → Prop) [DecidablePred target]
    (hpred : ∀ input, source input ↔ target (.inl input)) (bound : ℕ)
    (hbound : computation.IsQueryBoundP source bound) :
    (liftWorldToAdversary computation).IsQueryBoundP target bound := by
  induction computation using OracleComp.inductionOn generalizing bound with
  | pure value => simp [liftWorldToAdversary]
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      simp only [liftWorldToAdversary, simulateQ_bind, simulateQ_spec_query] at ih ⊢
      rw [OracleComp.isQueryBoundP_query_bind_iff]
      constructor
      · simpa only [← hpred input] using hbound.1
      · intro answer
        simpa only [← hpred input] using ih answer _ (hbound.2 answer)

noncomputable def neighborMain (publicKey : PublicKey) : OracleComp (OracleWorld + SigningSpec) Forgery := do
  let answer ← liftM ((OracleWorld + SigningSpec).query (.inr neighborRequest))
  let signature ← liftWorldToAdversary (neighborAfterSigning publicKey answer)
  pure (neighborForgery signature)

noncomputable def neighborAdversary : Adversary := ⟨neighborMain⟩

noncomputable def neighborSufCmaAdversary : SUFCMA.Adversary OracleWorld PublicKey Message Generic.Signature lifetime :=
  ⟨neighborMain⟩

def neighborDirectBudget : ℕ := 1 + (neighborSearchSteps + (preimageSearchSteps + 1))

theorem worldPrivateSamples_hashBound {α : Type} (computation : ProbComp α)
    (predicate : HashInput → Prop) [DecidablePred predicate] :
    (worldPrivateSamples computation).IsQueryBoundP (Seeded.hashBad predicate) 0 := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [worldPrivateSamples]
  | query_bind input next ih =>
      simp only [worldPrivateSamples, simulateQ_bind, simulateQ_spec_query] at ih ⊢
      rw [OracleComp.isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (by simp [Seeded.hashBad]), fun answer => by simpa [Seeded.hashBad] using ih answer⟩

theorem neighborFinish_queryBound (publicKey : PublicKey) (original : Generic.Signature) (encoding : Encoding)
    (randomness : Randomness) (transfer : DigitTransfer encoding) (block : PreimagePrefix) :
    (neighborFinish publicKey original encoding randomness transfer block).IsQueryBoundP
      (fun _ => True) (preimageSearchSteps + 1) := by
  unfold neighborFinish
  refine OracleComp.isQueryBoundP_bind (findDigestPreimage_queryBound _ _ _) ?_
  intro answer _
  cases answer with
  | none => exact OracleComp.isQueryBoundP_pure _ _ _
  | some answer =>
      simpa only [bind_pure_comp, OracleComp.isQueryBoundP_map_iff] using
        advanceSignatureChain_queryBound publicKey.parameter neighborRequest.epoch original encoding transfer

theorem neighborAfterEncoding_queryBound (publicKey : PublicKey) (original : Generic.Signature) (encoding : Encoding) :
    (neighborAfterEncoding publicKey original encoding).IsQueryBoundP (Seeded.hashBad (fun _ => True))
      (neighborSearchSteps + (preimageSearchSteps + 1)) := by
  classical
  unfold neighborAfterEncoding
  refine OracleComp.isQueryBoundP_bind
    (OracleComp.IsQueryBoundP.liftComp_subSpec (fun _ => Iff.rfl) (findEncodingNeighbor_queryBound _ _ _ _)) ?_
  intro answer _
  cases answer with
  | none => exact OracleComp.isQueryBoundP_pure _ _ _
  | some answer =>
      rcases answer with ⟨position, output⟩
      dsimp only
      split
      · rw [← Nat.zero_add (preimageSearchSteps + 1)]
        refine OracleComp.isQueryBoundP_bind (worldPrivateSamples_hashBound _ _) ?_
        intro block _
        exact OracleComp.IsQueryBoundP.liftComp_subSpec (fun _ => Iff.rfl) (neighborFinish_queryBound _ _ _ _ _ _)
      · exact OracleComp.isQueryBoundP_pure _ _ _

theorem neighborAfterSigning_queryBound (publicKey : PublicKey) (answer : Option Generic.Signature) :
    (neighborAfterSigning publicKey answer).IsQueryBoundP (Seeded.hashBad (fun _ => True)) neighborDirectBudget := by
  cases answer with
  | none => exact OracleComp.isQueryBoundP_pure _ _ _
  | some original =>
      unfold neighborAfterSigning neighborDirectBudget
      refine OracleComp.isQueryBoundP_bind (n := 1) (m := neighborSearchSteps + (preimageSearchSteps + 1)) ?_ ?_
      · apply OracleComp.IsQueryBoundP.liftComp_subSpec (fun _ => Iff.rfl)
        unfold Generic.Concrete.encodingHash Generic.Concrete.tweakableHash Generic.Concrete.oracleHash
        simp
      · intro digest _
        split
        · exact OracleComp.isQueryBoundP_pure _ _ _
        · exact neighborAfterEncoding_queryBound _ _ _

theorem findEncodingNeighbor_noSeed (parameter : PublicParameter) (leafIndex : LeafIndex)
    (message : Message) (encoding : Encoding) :
    (findEncodingNeighbor parameter leafIndex message encoding).IsQueryBoundP MaySeedHit 0 := by
  unfold findEncodingNeighbor
  apply Attack.findHash_queryBound_zero
  intro i _ _
  exact not_maySeedHit_tweakableHashInput _ _ _

theorem findDigestPreimage_chain_noSeed (parameter : PublicParameter) (leafIndex : LeafIndex)
    (chain : ChainIndex) (step : ChainStep) (target : Digest) (block : PreimagePrefix) :
    (findDigestPreimage (Concrete.CacheView.chainInput parameter leafIndex chain step) target block).IsQueryBoundP MaySeedHit 0 := by
  unfold findDigestPreimage
  apply Attack.findHash_queryBound_zero
  intro i _ _
  exact not_maySeedHit_tweakableHashInput _ _ _

theorem neighborFinish_noSeed (publicKey : PublicKey) (original : Generic.Signature) (encoding : Encoding)
    (randomness : Randomness) (transfer : DigitTransfer encoding) (block : PreimagePrefix) :
    (neighborFinish publicKey original encoding randomness transfer block).IsQueryBoundP MaySeedHit 0 := by
  unfold neighborFinish
  refine OracleComp.isQueryBoundP_bind (m := 0) (findDigestPreimage_chain_noSeed _ _ _ _ _ _) ?_
  intro answer _
  cases answer with
  | none => exact OracleComp.isQueryBoundP_pure _ _ _
  | some answer =>
      simp only [bind_pure_comp, OracleComp.isQueryBoundP_map_iff]
      exact Concrete.tweakableHash_noSeed _ _ _

theorem neighborAfterEncoding_noSeed (publicKey : PublicKey) (original : Generic.Signature) (encoding : Encoding) :
    (neighborAfterEncoding publicKey original encoding).IsQueryBoundP (Seeded.hashBad MaySeedHit) 0 := by
  classical
  unfold neighborAfterEncoding
  refine OracleComp.isQueryBoundP_bind (m := 0)
    (Seeded.liftM_hash_noSeed _ (findEncodingNeighbor_noSeed _ _ _ _)) ?_
  intro answer _
  cases answer with
  | none => exact OracleComp.isQueryBoundP_pure _ _ _
  | some answer =>
      rcases answer with ⟨position, output⟩
      dsimp only
      split
      · refine OracleComp.isQueryBoundP_bind (m := 0) (worldPrivateSamples_hashBound _ _) ?_
        intro block _
        exact Seeded.liftM_hash_noSeed _ (neighborFinish_noSeed _ _ _ _ _ _)
      · exact OracleComp.isQueryBoundP_pure _ _ _

theorem neighborAfterSigning_noSeed (publicKey : PublicKey) (answer : Option Generic.Signature) :
    (neighborAfterSigning publicKey answer).IsQueryBoundP (Seeded.hashBad MaySeedHit) 0 := by
  cases answer with
  | none => exact OracleComp.isQueryBoundP_pure _ _ _
  | some original =>
      unfold neighborAfterSigning
      refine OracleComp.isQueryBoundP_bind (m := 0)
        (Seeded.liftM_hash_noSeed _ (Concrete.encodingHash_noSeed _ _ _ _)) ?_
      intro digest _
      split
      · exact OracleComp.isQueryBoundP_pure _ _ _
      · exact neighborAfterEncoding_noSeed _ _ _

/-- info: 'XmssSecurity.TargetSum.Attack.neighborAfterSigning_noSeed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms neighborAfterSigning_noSeed

end XmssSecurity.TargetSum.Attack
