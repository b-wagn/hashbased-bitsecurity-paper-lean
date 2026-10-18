import XmssSecurity.Proof.Generic.Direct.DecidingOrientation
import XmssSecurity.Proof.Checksum.NoSign.IdealCoupling
import XmssSecurity.Proof.Generic.Direct.Basic
import XmssSecurity.Proof.Checksum.Code
import XmssSecurity.Proof.Checksum.EncodingProbability
/-!
# Adversaries without signing requests

An adversary whose program contains no signing request (`NoSign`) runs in the game as the
program with every oracle forwarded (`forwardPhase`) and an empty signing log
(`adversaryPhase_eq_of_noSign`). With `D` direct hash queries, every run of it from a cache adds
at most `D` inputs to the cache (`exists_list_of_forwardPhase`).
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.Checksum.NoSign

/-- The signing requests among the adversary's actions. -/
def IsSignQuery : (OracleWorld + Generic.SigningSpec).Domain → Prop
  | .inr _ => True
  | .inl _ => False

instance : DecidablePred IsSignQuery := fun input => by
  rcases input with _ | _ <;> unfold IsSignQuery <;> infer_instance

/-- No signing request on any branch of the adversary's program. -/
def NoSignQueries (adversary : Generic.Adversary) : Prop :=
  ∀ publicKey, (adversary.main publicKey).IsQueryBoundP IsSignQuery 0

/-- Forward private sampling and hash queries. -/
def forwardWorld : QueryImpl OracleWorld (OracleComp OracleWorld) :=
  fun input => liftM (OracleWorld.query input)

/-- Answer every signing request by `none`. -/
def refuseSigning : QueryImpl Generic.SigningSpec (OracleComp OracleWorld) :=
  fun _ => pure none

/-- Forward private sampling and hash queries; answer a signing request, which a program without
signing requests never makes, by `none`. -/
def forwardOnly : QueryImpl (OracleWorld + Generic.SigningSpec) (OracleComp OracleWorld) :=
  forwardWorld + refuseSigning

/-- The adversary with every oracle forwarded. -/
noncomputable def forwardPhase (adversary : Generic.Adversary) (publicKey : PublicKey) :
    OracleComp OracleWorld Generic.Forgery :=
  simulateQ forwardOnly (adversary.main publicKey)

theorem simulateQ_run_eq_forwardOnly {Key α : Type} (scheme : Generic.Scheme Key) (secretKey : Key)
    (computation : OracleComp (OracleWorld + Generic.SigningSpec) α)
    (hcomputation : computation.IsQueryBoundP IsSignQuery 0) :
    (simulateQ (Generic.forwardOracles + Generic.signingOracle scheme secretKey) computation).run =
      (fun value => (value, ([] : QueryLog Generic.SigningSpec))) <$>
        simulateQ forwardOnly computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hcomputation
      rcases input with world | request
      · have hnext : ∀ answer, (next answer).IsQueryBoundP IsSignQuery 0 := fun answer => by
          simpa [IsSignQuery] using hcomputation.2 answer
        simp only [simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inl,
          WriterT.run_bind, Generic.forwardOracles, forwardOnly, forwardWorld, map_bind]
        simp only [ih _ (hnext _), Functor.map_map]
        rfl
      · simp [IsSignQuery] at hcomputation

/-- The adversary phase of the game for an adversary without signing requests. -/
theorem adversaryPhase_eq_of_noSign (adversary : Generic.Adversary) (hno : NoSignQueries adversary)
    (publicKey : PublicKey) (secretKey : Generic.SecretKey) :
    Generic.Deciding.adversaryPhase adversary publicKey secretKey =
      (fun forgery => (forgery, ([] : QueryLog Generic.SigningSpec))) <$>
        forwardPhase adversary publicKey :=
  simulateQ_run_eq_forwardOnly Generic.Concrete.scheme secretKey _ (hno publicKey)

/-- The hash queries of a world program. -/
def IsWorldHashQuery : OracleWorld.Domain → Prop
  | .inr _ => True
  | .inl _ => False

instance : DecidablePred IsWorldHashQuery := fun input => by
  rcases input with _ | _ <;> unfold IsWorldHashQuery <;> infer_instance

theorem forwardOnly_isQueryBoundP {α : Type}
    (computation : OracleComp (OracleWorld + Generic.SigningSpec) α) (budget : ℕ)
    (hcomputation : computation.IsQueryBoundP Generic.Direct.IsDirectHashQuery budget) :
    (simulateQ forwardOnly computation).IsQueryBoundP IsWorldHashQuery budget := by
  induction computation using OracleComp.inductionOn generalizing budget with
  | pure value => simp
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hcomputation
      rw [simulateQ_query_bind]
      rcases input with (uniformInput | hashInput) | request
      · refine (isQueryBoundP_query_bind_iff (spec := OracleWorld) IsWorldHashQuery (.inl uniformInput) _ _).2
          ⟨Or.inl (by simp [IsWorldHashQuery]), fun answer => ?_⟩
        simpa [IsWorldHashQuery] using ih answer budget (by simpa using hcomputation.2 answer)
      · have hpositive : 0 < budget := by simpa using hcomputation.1
        refine (isQueryBoundP_query_bind_iff (spec := OracleWorld) IsWorldHashQuery (.inr hashInput) _ _).2
          ⟨Or.inr hpositive, fun answer => ?_⟩
        simpa [IsWorldHashQuery] using
          ih answer (budget - 1) (by simpa using hcomputation.2 answer)
      · change (pure none >>= fun answer => simulateQ forwardOnly (next answer)).IsQueryBoundP
          IsWorldHashQuery budget
        rw [pure_bind]
        exact ih none budget (by simpa using hcomputation.2 none)

theorem forwardPhase_isQueryBoundP (adversary : Generic.Adversary) (D : ℕ)
    (hD : Generic.Direct.IsDirectQueryBound adversary D) (publicKey : PublicKey) :
    (forwardPhase adversary publicKey).IsQueryBoundP IsWorldHashQuery D :=
  forwardOnly_isQueryBoundP _ D (hD publicKey)

/-- A run with at most `budget` hash queries adds at most `budget` inputs to the cache. -/
theorem exists_list_of_isQueryBoundP {α : Type} (computation : OracleComp OracleWorld α)
    (budget : ℕ) (hcomputation : computation.IsQueryBoundP IsWorldHashQuery budget)
    (cache : QueryCache HashSpec) (result : α × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ Generic.romImpl computation).run cache)) :
    ∃ inputs : List HashInput, inputs.length ≤ budget ∧
      ∀ input, result.2 input ≠ none → cache input ≠ none ∨ input ∈ inputs := by
  induction computation using OracleComp.inductionOn generalizing budget cache with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨[], by simp, fun input hinput => Or.inl hinput⟩
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at hcomputation
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hresult
      obtain ⟨first, hfirst, hrest⟩ := hresult
      rcases query with uniformIndex | hashInput
      · have hcache : first.2 = cache := by
          change first ∈ support ((simulateQ Generic.romImpl
            (liftM (OracleWorld.query (.inl uniformIndex)))).run cache) at hfirst
          simp [Generic.romImpl, unifFwdImpl, QueryImpl.liftTarget_apply,
            HasQuery.toQueryImpl_apply] at hfirst
          obtain ⟨_, rfl⟩ := hfirst
          rfl
        rw [hcache] at hrest
        exact ih first.1 budget (by simpa [IsWorldHashQuery] using hcomputation.2 first.1)
          cache hrest
      · have hpositive : 0 < budget := by simpa [IsWorldHashQuery] using hcomputation.1
        obtain ⟨inputs, hlength, hcover⟩ := ih first.1 (budget - 1)
          (by simpa [IsWorldHashQuery] using hcomputation.2 first.1) first.2 hrest
        refine ⟨hashInput :: inputs, by simp; omega, fun input hinput => ?_⟩
        rcases hcover input hinput with hfirstCache | hmem
        · by_cases heq : input = hashInput
          · exact Or.inr (by simp [heq])
          · left
            have hquery : first ∈ support ((randomOracle (spec := HashSpec) hashInput).run cache) := by
              simpa [Generic.romImpl] using hfirst
            cases hnone : cache hashInput with
            | some output =>
                rw [QueryImpl.withCaching_run_some _ hnone] at hquery
                simp only [support_pure, Set.mem_singleton_iff] at hquery
                rw [hquery] at hfirstCache
                exact hfirstCache
            | none =>
                rw [QueryImpl.withCaching_run_none _ hnone, support_map] at hquery
                obtain ⟨output, _, rfl⟩ := hquery
                dsimp only at hfirstCache
                rwa [QueryCache.cacheQuery_of_ne _ _ heq] at hfirstCache
        · exact Or.inr (List.mem_cons_of_mem _ hmem)

end XmssSecurity.Checksum.NoSign
