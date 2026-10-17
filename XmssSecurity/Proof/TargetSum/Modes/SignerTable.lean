import XmssSecurity.Proof.TargetSum.Modes.SignerAccounting
import XmssSecurity.Proof.TargetSum.Deterministic.SignerPhaseCost

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Modes
open XmssSecurity.Modes

attribute [local irreducible] sampleMasterSeed

theorem signer_phase_eq_runSigning
    (adversary : Security.StatementAdversary) (publicKey : PublicKey)
    (secretKey : Seeded.SecretKey) :
    (simulateQ (Security.adversaryImpl secretKey) (adversary.main publicKey)).run =
      Seeded.runSigning (fun request => Seeded.sign secretKey request.epoch request.message)
        (DeterministicSigning.withRequestLog (adversary.main publicKey)) := by
  rw [Seeded.runSigning_withRequestLog]
  rfl

/-- Presampling does not spend the adversary's budget. Every resulting table execution
still pays for both hashes of each signing attempt. -/
theorem signer_tablePhaseCost_le_after_preparation
    {β : Type} (adversary : Security.StatementAdversary) (q : Nat)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound xmss adversary q)
    (publicKey : PublicKey) (secretKey : Seeded.SecretKey) (cache : QueryCache HashSpec)
    (hkey : ((publicKey, secretKey), cache) ∈ support ((simulateQ romImpl xmss.keygen).run ∅))
    (preparation : OracleComp OracleWorld β) (prepared : β × QueryCache HashSpec)
    (hprepared : prepared ∈ support ((simulateQ romImpl preparation).run cache))
    (randomizers : Seeded.RandomizerOutputs)
    (hcache : ∀ position, prepared.2
      (Seeded.randomizerInputs secretKey.precomputed.parameter secretKey.seed position) =
        some (randomizers position))
    (result : (Forgery × QueryLog SigningSpec) × Seeded.CostState)
    (hresult : result ∈ support
      ((simulateQ (Seeded.tablePhaseCostImpl randomizers secretKey.precomputed)
        (DeterministicSigning.withRequestLog (adversary.main publicKey))).run (prepared.2, 0))) :
    result.2.2 ≤ q := by
  have hphase := signer_adversaryPhase_hashQueryBound adversary q hbound publicKey secretKey cache hkey
  rw [signer_phase_eq_runSigning] at hphase
  have hphasePrepared := Seeded.hashQueryBound_after_preparation _ preparation cache q hphase
    prepared hprepared
  exact Seeded.tablePhaseCost_le_of_hashQueryBound secretKey.seed secretKey.precomputed
    randomizers _ prepared.2 hcache q hphasePrepared result hresult

/-- info: 'XmssSecurity.TargetSum.Modes.signer_tablePhaseCost_le_after_preparation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signer_tablePhaseCost_le_after_preparation

end XmssSecurity.TargetSum.Modes
