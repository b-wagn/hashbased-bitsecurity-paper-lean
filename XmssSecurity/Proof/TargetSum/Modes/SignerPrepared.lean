import XmssSecurity.Proof.TargetSum.Modes.SignerTable
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! The statement's phase budget remains valid when cache entries are presampled before
the complete counted game, including before key generation. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Modes
open XmssSecurity.Modes

attribute [local irreducible] Generic.sampleMasterSeed

theorem signer_adversaryPhase_hashQueryBound_after_initial_preparation
    {β : Type} (adversary : Generic.Security.StatementAdversary) (q : Nat)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound Generic.xmss adversary q)
    (preparation : OracleComp OracleWorld β) (prepared : β × QueryCache HashSpec)
    (hprepared : prepared ∈ support ((simulateQ Generic.romImpl preparation).run ∅))
    (publicKey : PublicKey) (secretKey : Generic.Seeded.SecretKey) (cache : QueryCache HashSpec)
    (hkey : ((publicKey, secretKey), cache) ∈
      support ((simulateQ Generic.romImpl Generic.xmss.keygen).run prepared.2)) :
    Generic.HashQueryBound ((simulateQ (Generic.Security.adversaryImpl secretKey)
      (adversary.main publicKey)).run) cache q := by
  rw [Generic.hashQueryBound_iff_run]
  rintro ⟨⟨⟨forgery, log⟩, charged⟩, finalCache⟩ hadversary
  obtain ⟨verification, hverification⟩ := Generic.probComp_support_nonempty
    ((simulateQ Generic.romImpl (Generic.xmss.verify publicKey forgery.epoch forgery.message
      forgery.signature)).run finalCache)
  apply hbound (decide (Generic.SigningTranscript.Valid log ∧ ¬Generic.SigningTranscript.Contains log forgery) &&
    verification.1, charged)
  simp only [SUFCMA.notion, RandomOracleModel.run]
  rw [← Generic.Security.romImpl_eq, mem_support_iff_of_evalDist_eq
    (Generic.Seeded.evalDist_presample_computation _ preparation ∅), mem_support_bind_iff]
  refine ⟨prepared, hprepared, ?_⟩
  rw [gameCounted_signer_eq, StateT.run'_eq, support_map]
  refine ⟨((decide (Generic.SigningTranscript.Valid log ∧ ¬Generic.SigningTranscript.Contains log forgery) &&
    verification.1, charged), verification.2), ?_, rfl⟩
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
  exact ⟨((publicKey, secretKey), cache), hkey, (((forgery, log), charged), finalCache),
    hadversary, verification, hverification, by simp⟩

/-- info: 'XmssSecurity.TargetSum.Modes.signer_adversaryPhase_hashQueryBound_after_initial_preparation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signer_adversaryPhase_hashQueryBound_after_initial_preparation

end XmssSecurity.TargetSum.Modes
