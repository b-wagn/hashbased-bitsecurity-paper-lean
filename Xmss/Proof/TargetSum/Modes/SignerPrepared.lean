import Xmss.Proof.TargetSum.Modes.SignerTable
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! The statement's phase budget remains valid when cache entries are presampled before
the complete counted game, including before key generation. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum.Modes
open Xmss.Modes

attribute [local irreducible] Generic.sampleMasterSeed

theorem signer_adversaryPhase_hashQueryBound_after_initial_preparation
    {β : Type} (adversary : AdversaryBridge.StatementAdversary) (q : Nat)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound Generic.xmss adversary q)
    (preparation : OracleComp OracleWorld β) (prepared : β × QueryCache HashSpec)
    (hprepared : prepared ∈ support ((simulateQ romImpl preparation).run ∅))
    (publicKey : PublicKey) (secretKey : Generic.Seeded.SecretKey) (cache : QueryCache HashSpec)
    (hkey : ((publicKey, secretKey), cache) ∈
      support ((simulateQ romImpl Generic.xmss.keygen).run prepared.2)) :
    HashQueryBound ((simulateQ (AdversaryBridge.adversaryImpl secretKey)
      (adversary.main publicKey)).run) cache q := by
  rw [hashQueryBound_iff_run]
  rintro ⟨⟨⟨forgery, log⟩, charged⟩, finalCache⟩ hadversary
  obtain ⟨verification, hverification⟩ := probComp_support_nonempty
    ((simulateQ romImpl (Generic.xmss.verify publicKey forgery.epoch forgery.message
      forgery.signature)).run finalCache)
  apply hbound (decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) &&
    verification.1, charged)
  simp only [SUFCMA.notion, RandomOracleModel.run]
  rw [← AdversaryBridge.romImpl_eq, mem_support_iff_of_evalDist_eq
    (Seeded.evalDist_presample_computation _ preparation ∅), mem_support_bind_iff]
  refine ⟨prepared, hprepared, ?_⟩
  rw [gameCounted_signer_eq, StateT.run'_eq, support_map]
  refine ⟨((decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) &&
    verification.1, charged), verification.2), ?_, rfl⟩
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
  exact ⟨((publicKey, secretKey), cache), hkey, (((forgery, log), charged), finalCache),
    hadversary, verification, hverification, by simp⟩

/-- info: 'Xmss.TargetSum.Modes.signer_adversaryPhase_hashQueryBound_after_initial_preparation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signer_adversaryPhase_hashQueryBound_after_initial_preparation

end Xmss.TargetSum.Modes
