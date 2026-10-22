import SlhDsaSecurity.Proof.CarrierRecordings
import SlhDsaSecurity.Proof.SignerRightRecord
import SlhDsaSecurity.Proof.LateProvenance

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
  CarriedWitness RecordedQueries

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
  · obtain ⟨mid, hstart, hlater, habsent, hkeep, -⟩ := hentries entry hnew
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

/-! ## The two outer phases

Each asks its question of the object that can answer it, as at the shared oracle — key
generation's is about an input's shape and the verifier's is about who asked, and both are the
shared oracle's to answer. The projection is **stronger** here than `SplitPrefix.mem_support_rom`
was: `ServingForget.ForgetsAlong` is an equality of computations, so the shared oracle's run is
not merely reachable from the carrier's but equal to its image. -/

set_option maxHeartbeats 1000000 in
/-- **A carrier run projects onto the shared oracle's**, by the equality the handler was given. -/
theorem mem_support_rom_of_carrier (rightKeep : Bytes → HandlerCarrier.State → Prop)
    {α : Type} (computation : OracleComp OracleWorld α) (state : CountedState)
    (result : α × CountedState)
    (hresult : result ∈ support ((simulateQ (countedCarrierRecorder pk rightKeep)
      computation).run state)) :
    (result.1, result.2.1.cache) ∈
      support ((simulateQ KeygenUniform.rom computation).run state.1.cache) := by
  have hforget := forgetsAlong_countedCarrierRecorder pk rightKeep computation state
  rw [show ((simulateQ KeygenUniform.rom computation).run state.1.cache) =
    (simulateQ KeygenUniform.rom computation).run
      ((fun state : CountedState =>
        RecorderView.CacheView.cacheOf (state.1, state.2.1).1) state) from rfl,
    ← hforget, support_map]
  exact ⟨result, hresult, rfl⟩

set_option maxHeartbeats 1000000 in
/-- **An entry key generation files as a target is one of its own probes.** -/
theorem keygen_right_record (rightKeep : Bytes → HandlerCarrier.State → Prop)
    (secretSeed prfSeed publicSeed : Digest) (state : CountedState)
    (result : (SecretKey × PublicKey) × CountedState)
    (hresult : result ∈ support ((simulateQ (countedCarrierRecorder pk rightKeep)
      (Scheme.keygenInternal (m := OracleComp OracleWorld)
        secretSeed prfSeed publicSeed)).run state))
    (later : QueryCache HashSpec)
    (hlater : ∀ (probe : Bytes) (value : HashOutput),
      result.2.1.cache probe = some value → later probe = some value)
    (entry : Bytes × HashOutput) (hentry : entry ∈ result.2.2.1.2) :
    entry ∈ state.2.1.2 ∨ CacheReplay.QueriesUnder later
      (Scheme.keygenInternal (m := OracleComp HashSpec) secretSeed prfSeed publicSeed)
      entry.1 := by
  classical
  obtain ⟨suffix, hsuffix, hentries⟩ := run_right_suffix pk rightKeep _ state result hresult
  rw [hsuffix] at hentry
  rcases List.mem_append.mp hentry with hprior | hnew
  · exact Or.inl hprior
  · obtain ⟨mid, hstart, -, habsent, -, hfinal⟩ := hentries entry hnew
    have hfresh : state.1.cache entry.1 = none := by
      rcases hstate : state.1.cache entry.1 with _ | value
      · rfl
      · rw [hstart entry.1 value hstate] at habsent
        exact absurd habsent (by simp)
    exact Or.inr (CacheProvenance.queriesUnder_keygenInternal_of_fresh secretSeed prfSeed
      publicSeed state.1.cache result.2.1.cache later result.1
      (mem_support_rom_of_carrier pk rightKeep _ state result hresult) hlater entry.1 hfresh
      (Option.ne_none_iff_exists'.mpr ⟨entry.2, hfinal⟩))

set_option maxHeartbeats 1000000 in
/-- **An entry the verifier files as a target is one of its own queries**, hence in the record it
keeps. -/
theorem verify_right_record (rightKeep : Bytes → HandlerCarrier.State → Prop)
    (key : PublicKey) (message : Message) (signature : Bytes) (state : CountedState)
    (result : (Bool × Tally) × CountedState)
    (hresult : result ∈ support ((simulateQ (countedCarrierRecorder pk rightKeep)
      (countRecorded verifierCost (Scheme.verify key message signature))).run state))
    (entry : Bytes × HashOutput) (hentry : entry ∈ result.2.2.1.2) :
    entry ∈ state.2.1.2 ∨ entry.1 ∈ result.1.2.2 := by
  classical
  obtain ⟨suffix, hsuffix, hentries⟩ := run_right_suffix pk rightKeep _ state result hresult
  rw [hsuffix] at hentry
  rcases List.mem_append.mp hentry with hprior | hnew
  · exact Or.inl hprior
  · obtain ⟨mid, hstart, -, habsent, -, hfinal⟩ := hentries entry hnew
    have hfresh : state.1.cache entry.1 = none := by
      rcases hstate : state.1.cache entry.1 with _ | value
      · rfl
      · rw [hstart entry.1 value hstate] at habsent
        exact absurd habsent (by simp)
    exact Or.inr (LateProvenance.mem_record_countRecorded _ state.1.cache
      (result.1, result.2.1.cache)
      (mem_support_rom_of_carrier pk rightKeep _ state result hresult) entry.1 hfresh
      (Option.ne_none_iff_exists'.mpr ⟨entry.2, hfinal⟩))

end SlhDsaSecurity.CarrierSignRecord
