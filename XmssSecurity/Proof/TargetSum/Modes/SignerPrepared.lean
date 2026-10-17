import XmssSecurity.Proof.TargetSum.Modes.SignerTable

/-! The statement's phase budget remains valid when cache entries are presampled before
the complete counted game, including before key generation. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Modes
open XmssSecurity.Modes

attribute [local irreducible] sampleMasterSeed

theorem signer_adversaryPhase_hashQueryBound_after_initial_preparation
    {β : Type} (adversary : Security.StatementAdversary) (q : Nat)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound xmss adversary q)
    (preparation : OracleComp OracleWorld β) (prepared : β × QueryCache HashSpec)
    (hprepared : prepared ∈ support ((simulateQ romImpl preparation).run ∅))
    (publicKey : PublicKey) (secretKey : Seeded.SecretKey) (cache : QueryCache HashSpec)
    (hkey : ((publicKey, secretKey), cache) ∈
      support ((simulateQ romImpl xmss.keygen).run prepared.2)) :
    HashQueryBound ((simulateQ (Security.adversaryImpl secretKey)
      (adversary.main publicKey)).run) cache q := by
  rw [hashQueryBound_iff_run]
  rintro ⟨⟨⟨forgery, log⟩, charged⟩, finalCache⟩ hadversary
  obtain ⟨verification, hverification⟩ := probComp_support_nonempty
    ((simulateQ romImpl (xmss.verify publicKey forgery.epoch forgery.message
      forgery.signature)).run finalCache)
  apply hbound (decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) &&
    verification.1, charged)
  simp only [SUFCMA.notion, RandomOracleModel.run]
  rw [← Security.romImpl_eq, mem_support_iff_of_evalDist_eq
    (Seeded.evalDist_presample_computation _ preparation ∅), mem_support_bind_iff]
  refine ⟨prepared, hprepared, ?_⟩
  rw [gameCounted_signer_eq, StateT.run'_eq, support_map]
  refine ⟨((decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) &&
    verification.1, charged), verification.2), ?_, rfl⟩
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
  exact ⟨((publicKey, secretKey), cache), hkey, (((forgery, log), charged), finalCache),
    hadversary, verification, hverification, by simp⟩

/-- info: 'XmssSecurity.TargetSum.Modes.signer_adversaryPhase_hashQueryBound_after_initial_preparation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signer_adversaryPhase_hashQueryBound_after_initial_preparation

end XmssSecurity.TargetSum.Modes
