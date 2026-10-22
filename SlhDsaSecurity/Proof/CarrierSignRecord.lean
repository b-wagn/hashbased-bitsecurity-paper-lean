import SlhDsaSecurity.Proof.CarrierRecordings
import SlhDsaSecurity.Proof.SignerRightRecord

/-!
# What a signing sub-run can file as a target, at the carrier

`SignerRightRecord` says this at the shared oracle's recorder. Here it is at the handler the
obligations are moving to, and it is assembly rather than argument: the cut is generic in the
handler (`run_signInternal_at`), the randomiser's answer is in the cache after its own query
(`Files.hashCached`), and every entry the rest files comes with the carrier it was filed at
(`run_right_suffix`), which extends the one that query left.

So every such carrier holds the randomiser's answer, with no ordering established and no step
named — the same escape as at the shared oracle, for the same reason: the lemma quantifies over
the states the rest reached instead of picking one.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.CarrierSignRecord

open Security BracketedRun CarrierFiles CarrierRecordings SignerRightRecord CountedHandler
  CarriedWitness

variable (pk : PublicKey)

set_option maxHeartbeats 1000000 in
/-- **A served request files, as a target, only its own randomiser probe or an entry whose
carrier already held that request's randomiser answer.** -/
theorem signInternal_right_record (rightKeep : Bytes → HandlerCarrier.State → Prop)
    (sk : SecretKey) (message : Bytes) (state : CountedState)
    (result : Signature × CountedState)
    (hresult : result ∈ support ((simulateQ (countedCarrierRecorder pk rightKeep)
      (Scheme.signInternal (m := OracleComp OracleWorld) sk message)).run state))
    (entry : Bytes × HashOutput) (hentry : entry ∈ result.2.2.1.2) :
    entry ∈ state.2.1.2 ∨
      entry.1 = Hashing.randomizerInput sk.prf sk.publicKey.seed message ∨
      ∃ (mid : HandlerCarrier.State) (answer : HashOutput),
        mid.cache (Hashing.randomizerInput sk.prf sk.publicKey.seed message) = some answer ∧
          (∀ (probe : Bytes) (value : HashOutput),
            mid.cache probe = some value → result.2.1.cache probe = some value) ∧
            mid.cache entry.1 = none ∧
              rightKeep entry.1 (servingNotice pk mid entry.1) := by
  classical
  rw [run_signInternal_at, mem_support_bind_iff] at hresult
  obtain ⟨step, hstep, hrest⟩ := hresult
  -- The randomiser's answer is in the carrier the first step leaves.
  have hcached : step.2.1.cache (Hashing.randomizerInput sk.prf sk.publicKey.seed message) =
      some step.1 :=
    (files_countedCarrierRecorder pk rightKeep).hashCached _ state step hstep
  -- What the rest of the signer filed, each with the carrier it was filed at.
  obtain ⟨suffix, hsuffix, hentries⟩ :=
    run_right_suffix pk rightKeep _ step.2 result hrest
  rw [hsuffix] at hentry
  rcases List.mem_append.mp hentry with hold | hnew
  · -- Filed by the first step, if at all: its only input is the `PRF_msg` one.
    rcases step_right_shape pk rightKeep _ state step hstep with
      hsame | ⟨appended, answer, hqueried, hshape, -, -⟩
    · rw [hsame] at hold
      exact Or.inl hold
    · rw [hshape] at hold
      rcases List.mem_append.mp hold with hprior | hself
      · exact Or.inl hprior
      · refine Or.inr (Or.inl ?_)
        rw [List.mem_singleton.mp hself]
        exact (Sum.inr.injEq _ _).mp hqueried.symm
  · obtain ⟨mid, hstart, hlater, habsent, hkeep⟩ := hentries entry hnew
    exact Or.inr (Or.inr ⟨mid, step.1, hstart _ _ hcached, hlater, habsent, hkeep⟩)

set_option maxHeartbeats 1000000 in
/-- **A rejected request files nothing**, because it makes no query. -/
theorem sign_right_record_none (rightKeep : Bytes → HandlerCarrier.State → Prop)
    (sk : SecretKey) (request : Message) (hframe : request.frame = none)
    (state : CountedState) (result : Option Bytes × CountedState)
    (hresult : result ∈ support ((simulateQ (countedCarrierRecorder pk rightKeep)
      (Scheme.sign (m := OracleComp OracleWorld) sk request)).run state)) :
    result.2 = state := by
  rw [Scheme.sign, hframe, simulateQ_pure, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hresult
  rw [hresult]

set_option maxHeartbeats 1000000 in
/-- **And a served one files what its `signInternal` files.** -/
theorem sign_right_record (rightKeep : Bytes → HandlerCarrier.State → Prop)
    (sk : SecretKey) (request : Message) (framed : Bytes)
    (hframe : request.frame = some framed)
    (state : CountedState) (result : Option Bytes × CountedState)
    (hresult : result ∈ support ((simulateQ (countedCarrierRecorder pk rightKeep)
      (Scheme.sign (m := OracleComp OracleWorld) sk request)).run state))
    (entry : Bytes × HashOutput) (hentry : entry ∈ result.2.2.1.2) :
    entry ∈ state.2.1.2 ∨
      entry.1 = Hashing.randomizerInput sk.prf sk.publicKey.seed framed ∨
      ∃ (mid : HandlerCarrier.State) (answer : HashOutput),
        mid.cache (Hashing.randomizerInput sk.prf sk.publicKey.seed framed) = some answer ∧
          (∀ (probe : Bytes) (value : HashOutput),
            mid.cache probe = some value → result.2.1.cache probe = some value) ∧
            mid.cache entry.1 = none ∧
              rightKeep entry.1 (servingNotice pk mid entry.1) := by
  classical
  rw [Scheme.sign, hframe] at hresult
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hresult
  obtain ⟨inner, hinner, hvalue⟩ := hresult
  have hstate : result.2 = inner.2 := by rw [hvalue]
  rw [hstate] at hentry ⊢
  exact signInternal_right_record pk rightKeep sk framed state inner hinner entry hentry

end SlhDsaSecurity.CarrierSignRecord
