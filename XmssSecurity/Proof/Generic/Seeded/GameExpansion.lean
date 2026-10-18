import XmssSecurity.Proof.Generic.Seeded.KeygenSampling

open OracleComp OracleSpec

namespace XmssSecurity.Generic.Seeded

variable [Code]

set_option backward.isDefEq.respectTransparency false

noncomputable def gameAfterSecrets (adversary : Adversary) (parameter : PublicParameter)
    (secret : ChainSecrets) : OracleComp OracleWorld Bool := do
  let result ← liftM
    (Concrete.treeNode parameter secret treeHeight Concrete.rootNode : OracleComp HashSpec Digest).withQueryLog
  let sk := Concrete.precomputedSecretKey parameter secret (hashCacheOfLog result.2)
  gameRest Concrete.scheme adversary ⟨result.1, parameter⟩ sk

theorem gameCore_independent_eq (adversary : Adversary) :
    gameCore Concrete.scheme adversary = (do
      let parameter ← liftM Concrete.samplePublicParameter
      let secret ← liftM Concrete.sampleSecret
      gameAfterSecrets adversary parameter secret) := by
  simp only [gameCore, Concrete.scheme, Concrete.precomputedKeygen, gameAfterSecrets,
    gameRest, bind_assoc, pure_bind]

theorem run'_lift_hash_bind {A B : Type} (computation : OracleComp HashSpec A)
    (next : A → OracleComp OracleWorld B) (cache : QueryCache HashSpec) :
    (simulateQ romImpl ((liftM computation : OracleComp OracleWorld A) >>= next)).run' cache =
      ((simulateQ randomOracle computation).run cache >>= fun result =>
        (simulateQ romImpl (next result.1)).run' result.2) := by
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind]
  have h : simulateQ romImpl (liftM computation : OracleComp OracleWorld A) =
      simulateQ randomOracle computation :=
    QueryImpl.simulateQ_add_liftM_right _ _ computation
  rw [h, map_bind]
  rfl

theorem run'_lift_sample_bind {A B : Type} (computation : ProbComp A)
    (next : A → OracleComp OracleWorld B) (cache : QueryCache HashSpec) :
    (simulateQ romImpl ((liftM computation : OracleComp OracleWorld A) >>= next)).run' cache =
      (computation >>= fun result => (simulateQ romImpl (next result)).run' cache) := by
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind]
  have h : simulateQ romImpl (liftM computation : OracleComp OracleWorld A) =
      simulateQ (unifFwdImpl HashSpec) computation :=
    QueryImpl.simulateQ_add_liftM_left _ _ computation
  rw [h, unifFwdImpl.simulateQ_run]
  simp only [bind_map_left, map_bind]
  rfl

end XmssSecurity.Generic.Seeded
