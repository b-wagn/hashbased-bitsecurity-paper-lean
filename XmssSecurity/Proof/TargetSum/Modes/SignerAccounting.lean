import XmssSecurity.Proof.Common.Modes.AllHashes
import XmssSecurity.Proof.TargetSum.Modes.Keygen
import XmssSecurity.Proof.TargetSum.ExpectedCountedQueries

/-! Charge all hashes in the adversary phase, including the signer's hashes, while leaving
key generation and final verification outside the budget. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.TargetSum.Modes
open XmssSecurity.Modes

attribute [local irreducible] sampleMasterSeed

theorem signer_adversaryRun_counted
    (adversary : Security.StatementAdversary) (publicKey : PublicKey) (secretKey : Seeded.SecretKey) :
    (simulateQ
      ((QueryImpl.ofLift OracleWorld
        (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld))).withAddCost
          (RandomOracleModel.hashCost HashInput HashOutput) +
        SUFCMA.signingOracleCounted (RandomOracleModel.hashCost HashInput HashOutput) 0
          xmss secretKey) (adversary.main publicKey)).run.run =
      (fun result => ((result.1.1, Multiplicative.ofAdd result.2), result.1.2)) <$>
        countHashQueries ((simulateQ (Security.adversaryImpl secretKey)
          (adversary.main publicKey)).run) := by
  have h := simulateQ_adversaryRun (QueryImpl.id' OracleWorld)
    (RandomOracleModel.hashCost HashInput HashOutput) xmss secretKey adversary publicKey
  simp only [simulateQ_id'] at h
  have hcost : RandomOracleModel.hashCost HashInput HashOutput =
      fun input : OracleWorld.Domain => if input matches .inr _ then 1 else 0 := by
    funext input
    cases input <;> rfl
  let phase := (simulateQ (Security.adversaryImpl secretKey) (adversary.main publicKey)).run
  calc
    _ = swapLayers <$> (simulateQ
        ((QueryImpl.id' OracleWorld).withAddCost (RandomOracleModel.hashCost HashInput HashOutput))
        phase).run := h
    _ = (fun result => ((result.1.1, Multiplicative.ofAdd result.2), result.1.2)) <$>
        simulateQ (QueryImpl.id' OracleWorld) (countHashQueries phase) := by
      rw [countHashQueries, QueryCounting.simulate_withCost, hcost]
      rfl
    _ = _ := by rw [simulateQ_id']

theorem gameCounted_signer_eq (adversary : Security.StatementAdversary) :
    SUFCMA.gameCounted ⟨false, true, false, false⟩
      (RandomOracleModel.hashCost HashInput HashOutput) xmss adversary = (do
        let (publicKey, secretKey) ← xmss.keygen
        let ((forgery, log), charged) ← countHashQueries
          ((simulateQ (Security.adversaryImpl secretKey) (adversary.main publicKey)).run)
        let verified ← xmss.verify publicKey forgery.epoch forgery.message forgery.signature
        pure (decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) &&
          verified, charged)) := by
  unfold SUFCMA.gameCounted
  simp only [SUFCMA.costIf, Bool.false_eq_true, if_false, if_true, charge_zero,
    bind_map_left, zero_add, add_zero]
  apply bind_congr
  rintro ⟨publicKey, secretKey⟩
  rw [signer_adversaryRun_counted]
  simp only [bind_map_left, toAdd_ofAdd]

theorem signer_adversaryPhase_hashQueryBound
    (adversary : Security.StatementAdversary) (q : ℕ)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound xmss adversary q)
    (publicKey : PublicKey) (secretKey : Seeded.SecretKey) (cache : QueryCache HashSpec)
    (hkey : ((publicKey, secretKey), cache) ∈ support ((simulateQ romImpl xmss.keygen).run ∅)) :
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
  rw [← Security.romImpl_eq, gameCounted_signer_eq, StateT.run'_eq, support_map]
  refine ⟨((decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) &&
    verification.1, charged), verification.2), ?_, rfl⟩
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
  exact ⟨((publicKey, secretKey), cache), hkey, (((forgery, log), charged), finalCache),
    hadversary, verification, hverification, by simp⟩

theorem signer_expected_adversaryPhase_hashQueries_le
    (adversary : Security.StatementAdversary) (q : ℕ)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound xmss adversary q)
    (publicKey : PublicKey) (secretKey : Seeded.SecretKey) (cache : QueryCache HashSpec)
    (hkey : ((publicKey, secretKey), cache) ∈ support ((simulateQ romImpl xmss.keygen).run ∅)) :
    expectedSimulatedQueryCount romImpl IsHashQuery
      ((simulateQ (Security.adversaryImpl secretKey) (adversary.main publicKey)).run) cache ≤ q :=
  expectedHashQueries_le_of_hashQueryBound _ _ _
    (signer_adversaryPhase_hashQueryBound adversary q hbound publicKey secretKey cache hkey)

/-- info: 'XmssSecurity.TargetSum.Modes.signer_expected_adversaryPhase_hashQueries_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signer_expected_adversaryPhase_hashQueries_le

end XmssSecurity.TargetSum.Modes
