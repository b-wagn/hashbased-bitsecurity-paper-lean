import XmssSecurity.Proof.Common.Modes.AllHashes
import XmssSecurity.Proof.TargetSum.Modes.Keygen
import XmssSecurity.Proof.TargetSum.ExpectedCountedQueries
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Charge all hashes in the adversary phase, including the signer's hashes, while leaving
key generation and final verification outside the budget. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.TargetSum.Modes
open XmssSecurity.Modes

attribute [local irreducible] Generic.sampleMasterSeed

theorem signer_adversaryRun_counted
    (adversary : Generic.Security.StatementAdversary) (publicKey : PublicKey) (secretKey : Generic.Seeded.SecretKey) :
    (simulateQ
      ((QueryImpl.ofLift OracleWorld
        (WriterT (QueryLog Generic.SigningSpec) (OracleComp OracleWorld))).withAddCost
          (RandomOracleModel.hashCost HashInput HashOutput) +
        SUFCMA.signingOracleCounted (RandomOracleModel.hashCost HashInput HashOutput) 0
          Generic.xmss secretKey) (adversary.main publicKey)).run.run =
      (fun result => ((result.1.1, Multiplicative.ofAdd result.2), result.1.2)) <$>
        Generic.countHashQueries ((simulateQ (Generic.Security.adversaryImpl secretKey)
          (adversary.main publicKey)).run) := by
  have h := simulateQ_adversaryRun (QueryImpl.id' OracleWorld)
    (RandomOracleModel.hashCost HashInput HashOutput) Generic.xmss secretKey adversary publicKey
  simp only [simulateQ_id'] at h
  have hcost : RandomOracleModel.hashCost HashInput HashOutput =
      fun input : OracleWorld.Domain => if input matches .inr _ then 1 else 0 := by
    funext input
    cases input <;> rfl
  let phase := (simulateQ (Generic.Security.adversaryImpl secretKey) (adversary.main publicKey)).run
  calc
    _ = swapLayers <$> (simulateQ
        ((QueryImpl.id' OracleWorld).withAddCost (RandomOracleModel.hashCost HashInput HashOutput))
        phase).run := h
    _ = (fun result => ((result.1.1, Multiplicative.ofAdd result.2), result.1.2)) <$>
        simulateQ (QueryImpl.id' OracleWorld) (Generic.countHashQueries phase) := by
      rw [Generic.countHashQueries, QueryCounting.simulate_withCost, hcost]
      rfl
    _ = _ := by rw [simulateQ_id']

theorem gameCounted_signer_eq (adversary : Generic.Security.StatementAdversary) :
    SUFCMA.gameCounted ⟨false, true, false, false⟩
      (RandomOracleModel.hashCost HashInput HashOutput) Generic.xmss adversary = (do
        let (publicKey, secretKey) ← Generic.xmss.keygen
        let ((forgery, log), charged) ← Generic.countHashQueries
          ((simulateQ (Generic.Security.adversaryImpl secretKey) (adversary.main publicKey)).run)
        let verified ← Generic.xmss.verify publicKey forgery.epoch forgery.message forgery.signature
        pure (decide (Generic.SigningTranscript.Valid log ∧ ¬Generic.SigningTranscript.Contains log forgery) &&
          verified, charged)) := by
  unfold SUFCMA.gameCounted
  simp only [SUFCMA.costIf, Bool.false_eq_true, if_false, if_true, charge_zero,
    bind_map_left, zero_add, add_zero]
  apply bind_congr
  rintro ⟨publicKey, secretKey⟩
  rw [signer_adversaryRun_counted]
  simp only [bind_map_left, toAdd_ofAdd]

end XmssSecurity.TargetSum.Modes
