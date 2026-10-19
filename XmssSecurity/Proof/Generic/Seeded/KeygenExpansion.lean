import XmssSecurity.Proof.Generic.Seeded.FreshTable
import XmssSecurity.Proof.Generic.Seeded.SeedGuessing
import XmssSecurity.Proof.Generic.IdealStatement
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling
import VCVio.OracleComp.QueryTracking.Unpredictability

open OracleComp OracleSpec

namespace XmssSecurity.Generic.Seeded

variable [Code]

set_option backward.isDefEq.respectTransparency false

abbrev ChainSecrets := LeafIndex → ChainIndex → Digest

def chainInputs (parameter : PublicParameter) (seed : MasterSeed) (leafIndex : LeafIndex) (chain : ChainIndex) :
    HashInput := keygenHashInput parameter (.chain leafIndex chain) seed

theorem chainInputs_injective (parameter : PublicParameter) (seed : MasterSeed)
    (leafIndex leafIndex' : LeafIndex) (chain chain' : ChainIndex)
    (h : chainInputs parameter seed leafIndex chain = chainInputs parameter seed leafIndex' chain') :
    leafIndex = leafIndex' ∧ chain = chain' :=
  KeygenDomain.chain.inj (keygenHashInput_domain_seed_eq h).1

def parameterCache (seed : MasterSeed) (output : Digest) : QueryCache HashSpec :=
  (∅ : QueryCache HashSpec).cacheQuery (keygenHashInput 0 .parameter seed) output

theorem parameterCache_chain_fresh (seed : MasterSeed) (output : Digest)
    (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex) :
    parameterCache seed output (chainInputs parameter seed leafIndex chain) = none := by
  apply QueryCache.cacheQuery_of_ne
  intro h
  have hdomain := (keygenHashInput_domain_seed_eq h).1
  cases hdomain

def derivationCache (seed : MasterSeed) (parameterOutput : Digest) (outputs : ChainSecrets) :
    QueryCache HashSpec :=
  cacheRows (parameterCache seed parameterOutput) (chainInputs (parameterOutput) seed) outputs

def deriveChainSecrets (parameter : PublicParameter) (seed : MasterSeed) :
    OracleComp HashSpec (LeafIndex → ChainIndex → Digest) :=
  Concrete.sequenceFin fun leafIndex => Concrete.sequenceFin fun chain =>
    deriveKey parameter (.chain leafIndex chain) seed

noncomputable def drawChainSecrets : ProbComp ChainSecrets :=
  Concrete.sequenceFin fun _ : LeafIndex => Concrete.sequenceFin fun _ : ChainIndex => $ᵗ Digest

theorem deriveChainSecrets_eq_map (parameter : PublicParameter) (seed : MasterSeed) :
    deriveChainSecrets parameter seed =
      Concrete.sequenceFin (fun leafIndex => Concrete.sequenceFin fun chain =>
        (liftM (HashSpec.query (chainInputs parameter seed leafIndex chain)) : OracleComp HashSpec Digest)) := by
  simp only [deriveChainSecrets, deriveKey, Concrete.oracleHash, chainInputs]
  rfl

/-- The actual WOTS derivation loop, including its final cache, equals fresh full-output sampling. -/
theorem run_deriveChainSecrets (seed : MasterSeed) (parameterOutput : Digest) :
    (simulateQ randomOracle (deriveChainSecrets (parameterOutput) seed)).run
      (parameterCache seed parameterOutput) =
        (fun outputs => (outputs, derivationCache seed parameterOutput outputs)) <$>
          drawChainSecrets := by
  rw [deriveChainSecrets_eq_map,
    run_sequenceFin_rows_fresh _
      (fun leafIndex chain leafIndex' chain' => chainInputs_injective _ seed leafIndex leafIndex' chain chain')
      _ (parameterCache_chain_fresh seed parameterOutput _)]
  simp only [bind_pure_comp, Functor.map_map, drawChainSecrets, derivationCache]
  try rfl

theorem evalDist_drawChainSecrets : 𝒟[drawChainSecrets] = 𝒟[$ᵗ ChainSecrets] := by
  calc
    _ = 𝒟[Concrete.sequenceFin fun _ : LeafIndex => ($ᵗ (ChainIndex → Digest))] :=
      evalDist_sequenceFin_congr _ _ (fun _ => evalDist_sequenceFin_uniform _)
    _ = _ := evalDist_sequenceFin_uniform _

theorem evalDist_deriveChainSecrets (seed : MasterSeed) (parameterOutput : Digest) :
    𝒟[(simulateQ randomOracle (deriveChainSecrets (parameterOutput) seed)).run
      (parameterCache seed parameterOutput)] =
        𝒟[(fun outputs => (outputs, derivationCache seed parameterOutput outputs)) <$>
          ($ᵗ ChainSecrets)] := by
  rw [run_deriveChainSecrets, evalDist_map, evalDist_map, evalDist_drawChainSecrets]

def deriveParametersAndSecrets (seed : MasterSeed) :
    OracleComp HashSpec (PublicParameter × (LeafIndex → ChainIndex → Digest)) := do
  let parameter ← deriveKey 0 .parameter seed
  let secrets ← deriveChainSecrets parameter seed
  return (parameter, secrets)

theorem run_deriveParameter (seed : MasterSeed) :
    (simulateQ randomOracle (deriveKey 0 .parameter seed : OracleComp HashSpec Digest)).run ∅ =
      (fun output => (output, parameterCache seed output)) <$> ($ᵗ Digest) := by
  have hquery : (deriveKey 0 .parameter seed : OracleComp HashSpec Digest) =
      (liftM (HashSpec.query (keygenHashInput 0 .parameter seed)) :
        OracleComp HashSpec Digest) := rfl
  rw [hquery, simulateQ_spec_query, QueryImpl.withCaching_run_none _ (QueryCache.empty_apply _)]
  rfl

/-- Exact joint distribution of the derived values and every full answer retained by the oracle. -/
theorem evalDist_deriveParametersAndSecrets (seed : MasterSeed) :
    𝒟[(simulateQ randomOracle (deriveParametersAndSecrets seed)).run ∅] =
      𝒟[do
        let parameterOutput ← $ᵗ Digest
        let outputs ← $ᵗ ChainSecrets
        pure ((parameterOutput, outputs),
          derivationCache seed parameterOutput outputs)] := by
  simp only [deriveParametersAndSecrets, simulateQ_bind, simulateQ_pure,
    StateT.run_bind, StateT.run_pure]
  rw [run_deriveParameter]
  simp only [bind_map_left, bind_pure_comp]
  change 𝒟[($ᵗ Digest) >>= _] = 𝒟[($ᵗ Digest) >>= _]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameterOutput
  change 𝒟[(fun result => ((parameterOutput, result.1), result.2)) <$>
    (simulateQ randomOracle (deriveChainSecrets (parameterOutput) seed)).run
      (parameterCache seed parameterOutput)] = _
  rw [evalDist_map, evalDist_deriveChainSecrets, ← evalDist_map]
  simp only [Functor.map_map]

end XmssSecurity.Generic.Seeded
