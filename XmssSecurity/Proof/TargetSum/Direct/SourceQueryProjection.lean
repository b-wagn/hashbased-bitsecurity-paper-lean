import XmssSecurity.Proof.TargetSum.ExpectedQueryProjection
import XmssSecurity.Proof.TargetSum.Direct.SourceClassBudget
import XmssSecurity.Proof.TargetSum.Direct.FirstLaneSigningSupport
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! The counted source's selected query counts agree with the ordinary reference phase. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.CappedChain

theorem countedSource_expectedQuery_eq {α : Type} (publicKey : PublicKey) (secretKey : Generic.SecretKey)
    (selected : (OracleWorld + Generic.SigningSpec).Domain → Prop) [DecidablePred selected]
    (computation : OracleComp (OracleWorld + Generic.SigningSpec) α) (state : CountedSourceState) :
    expectedSimulatedQueryCount (countedSourceImpl secretKey) selected computation state =
      expectedSimulatedQueryCount (Generic.cappedUnloggedMappedAdversaryImpl publicKey secretKey)
        selected computation state.counts.cache :=
  expectedSimulatedQueryCount_eq_of_query_map_eq (countedSourceImpl secretKey)
    (Generic.cappedUnloggedMappedAdversaryImpl publicKey secretKey) (fun state => state.counts.cache)
    (countedSourceImpl_cache_projection publicKey secretKey) selected computation state

theorem reference_expectedClassBudget {α : Type} (publicKey : PublicKey) (secretKey : Generic.SecretKey)
    (targetCache initialCache : QueryCache HashSpec) (limit : Nat)
    (computation : OracleComp (OracleWorld + Generic.SigningSpec) α)
    (hbudget : CountedSourceBudget secretKey limit computation (CountedSourceState.initial initialCache)) :
    expectedSimulatedQueryCount (Generic.cappedUnloggedMappedAdversaryImpl publicKey secretKey)
        (Generic.Direct.IsDirectEncodingQuery secretKey.parameter) computation initialCache +
      expectedSimulatedQueryCount (Generic.cappedUnloggedMappedAdversaryImpl publicKey secretKey)
        (Generic.Direct.IsDirectStructuralQuery secretKey targetCache) computation initialCache +
      expectedSimulatedQueryCount (Generic.cappedUnloggedMappedAdversaryImpl publicKey secretKey)
        Direct.IsDirectSeedQuery computation initialCache +
      2 * (∑' result, Pr[= result | (simulateQ (countedSourceImpl secretKey) computation).run
        (CountedSourceState.initial initialCache)] * (result.2.counts.signing : ℝ≥0∞)) ≤ limit := by
  have h := countedSource_expectedClassBudget secretKey targetCache limit computation
    (CountedSourceState.initial initialCache) rfl hbudget
  simpa only [countedSource_expectedQuery_eq publicKey, CountedSourceState.initial] using h

/-- info: 'XmssSecurity.TargetSum.CappedChain.reference_expectedClassBudget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reference_expectedClassBudget

end XmssSecurity.TargetSum.CappedChain

namespace XmssSecurity.TargetSum.Direct

noncomputable def expectedSourceSignerHashes (adversary : Generic.Adversary) : ℝ≥0∞ :=
  ∑' keyResult, Pr[= keyResult | (simulateQ Generic.romImpl Generic.Concrete.scheme.keygen).run ∅] *
    ∑' result, Pr[= result | (simulateQ (CappedChain.countedSourceImpl keyResult.1.2)
      (adversary.main keyResult.1.1)).run (CappedChain.CountedSourceState.initial keyResult.2)] *
        (result.2.counts.signing : ℝ≥0∞)

end XmssSecurity.TargetSum.Direct
