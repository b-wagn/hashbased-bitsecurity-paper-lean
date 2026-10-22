import SlhDsaSecurity.Proof.SignerDigestStep

/-!
# What a signing sub-run can put in the target recording

`LateProvenance.hrecord`'s last branch needs that a target-recorded input is not the signer's own
digest query. The fact is true at the step the query is made from — `SignerDigestStep` proves
that much — and what has stood between the two is **granularity**: provenance inducts over the
phase, where one signing request is a single step, so the cache it can hand back is the one from
*before* the request, while the recorder files at the query *inside* it, after the randomiser.
Two lemmas can both hand back a state and still not be talking about the same step.

This file closes the gap at the sub-run, where both are in hand and neither has to be matched.
`Scheme.signInternal` is its randomiser query and then the rest, by
`SignerRandomiser.signInternal_eq`; after that first step the randomiser's answer is in the
cache, by `RecorderView.recorderOf_step_cache_self`; and `SplitPrefix.right_record_suffix`,
applied to **the rest**, says every entry the rest files comes with a cache that extends the one
the first step left. So every such cache holds the randomiser entry, with no ordering argument
and no step to name.

That leaves exactly one entry the first step itself could have filed — the `PRF_msg` input — and
`SplitWitness.narrowClass`'s last clause is what removes it, as its own docstring says.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.SignerRightRecord

open Security CacheAvailability SplitPrefix SignerRandomiser

/-- A hash query of the scheme's, simulated, is the implementation at that input. -/
theorem simulateQ_hash {σ : Type} (impl : QueryImpl OracleWorld (StateT σ ProbComp))
    (input : Bytes) :
    simulateQ impl (Hashing.hash (m := OracleComp OracleWorld) input) = impl (Sum.inr input) := by
  change simulateQ impl (liftM (OracleSpec.query (spec := OracleWorld) (Sum.inr input))) = _
  simp

set_option maxHeartbeats 800000 in
/-- **The signer, cut at its randomiser query, under the recorder.** -/
theorem run_signInternal (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (sk : SecretKey) (message : Bytes) (state : SplitState) :
    (simulateQ (recorder leftKeep rightKeep)
        (Scheme.signInternal (m := OracleComp OracleWorld) sk message)).run state =
      ((recorder leftKeep rightKeep)
          (Sum.inr (Hashing.randomizerInput sk.prf sk.publicKey.seed message))).run state >>=
        fun step =>
          (simulateQ (recorder leftKeep rightKeep)
            (signInternalAt (m := OracleComp OracleWorld) (Hashing.truncate step.1) sk
              message)).run step.2 := by
  rw [signInternal_eq sk message]
  simp only [Hashing.randomizer, Hashing.shortHash, bind_assoc, pure_bind,
    simulateQ_bind, StateT.run_bind, simulateQ_hash]
  rfl

set_option maxHeartbeats 800000 in
/-- **Every entry a signing sub-run files as a target comes with the randomiser entry already
cached** — or is the `PRF_msg` input itself, which the narrowing removes.

No ordering is established and no step is named. The first query installs the randomiser answer;
`right_record_suffix` on the rest hands back, for each entry it files, a cache extending the one
that query left. -/
theorem signInternal_right_record (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (sk : SecretKey) (message : Bytes) (state : SplitState) (result : Signature × SplitState)
    (hresult : result ∈ support ((simulateQ (recorder leftKeep rightKeep)
      (Scheme.signInternal (m := OracleComp OracleWorld) sk message)).run state)) :
    ∀ entry ∈ result.2.2.2, entry ∈ state.2.2 ∨
      entry.1 = Hashing.randomizerInput sk.prf sk.publicKey.seed message ∨
      ∃ (mid : QueryCache HashSpec) (answer : HashOutput),
        mid (Hashing.randomizerInput sk.prf sk.publicKey.seed message) = some answer ∧
          (∀ (probe : Bytes) (value : HashOutput),
            mid probe = some value → result.2.1 probe = some value) ∧
            mid entry.1 = none ∧ rightKeep entry.1 mid := by
  classical
  rw [run_signInternal, mem_support_bind_iff] at hresult
  obtain ⟨step, hstep, hrest⟩ := hresult
  -- The randomiser's answer is in the cache the first step leaves, whichever branch it took.
  have hcached : step.2.1 (Hashing.randomizerInput sk.prf sk.publicKey.seed message) =
      some step.1 := by
    rw [← RecorderView.recorderOf_cache leftKeep rightKeep] at hstep
    exact RecorderView.recorderOf_step_cache_self leftKeep rightKeep
      (Hashing.randomizerInput sk.prf sk.publicKey.seed message) state step hstep
  -- What the rest of the signer filed, each with a cache extending that one.
  obtain ⟨suffix, hsuffix, hentries⟩ :=
    right_record_suffix leftKeep rightKeep
      (signInternalAt (m := OracleComp OracleWorld) (Hashing.truncate step.1) sk message)
      step.2 result hrest
  intro entry hentry
  rw [hsuffix] at hentry
  rcases List.mem_append.mp hentry with hold | hnew
  · -- Filed by the first step, if at all: its only input is the `PRF_msg` one.
    have hstepRecord := RecorderView.recorderOf_step_record leftKeep rightKeep
      (Hashing.randomizerInput sk.prf sk.publicKey.seed message) state step
      (by rw [← RecorderView.recorderOf_cache leftKeep rightKeep] at *; exact hstep)
    rw [RecorderView.appendedOf_cache] at hstepRecord
    rw [show step.2.2 = appended leftKeep rightKeep
      (Hashing.randomizerInput sk.prf sk.publicKey.seed message) state step.1 from
        hstepRecord] at hold
    cases hcachedProbe : state.1 (Hashing.randomizerInput sk.prf sk.publicKey.seed message) with
    | some cached =>
      rw [appended_of_cached leftKeep rightKeep (Hashing.randomizerInput sk.prf sk.publicKey.seed message) state step.1 cached hcachedProbe] at hold
      exact Or.inl hold
    | none =>
      by_cases hleftProbe : leftKeep (Hashing.randomizerInput sk.prf sk.publicKey.seed message) state.1
      · rw [appended_of_left leftKeep rightKeep (Hashing.randomizerInput sk.prf sk.publicKey.seed message)
            state step.1 hcachedProbe hleftProbe] at hold
        exact Or.inl hold
      · by_cases hrightProbe : rightKeep (Hashing.randomizerInput sk.prf sk.publicKey.seed message) state.1
        · rw [appended_of_right leftKeep rightKeep
            (Hashing.randomizerInput sk.prf sk.publicKey.seed message) state step.1 hcachedProbe
            hleftProbe hrightProbe] at hold
          rcases List.mem_append.mp hold with hprior | hself
          · exact Or.inl hprior
          · exact Or.inr (Or.inl (by rw [List.mem_singleton.mp hself]))
        · rw [appended_of_neither leftKeep rightKeep
            (Hashing.randomizerInput sk.prf sk.publicKey.seed message) state step.1 hleftProbe
            hrightProbe] at hold
          exact Or.inl hold
  · obtain ⟨mid, hstart, hlater, habsent, hkeep, -⟩ := hentries entry hnew
    exact Or.inr (Or.inr ⟨mid, step.1, hstart _ _ hcached, hlater, habsent, hkeep⟩)

/-! ## At the request, which is where provenance names it

`Scheme.sign` is the framing test and then `signInternal`, so a served request files exactly what
its `signInternal` files and a rejected one files nothing. Stated here so that whoever mirrors
the phase decomposition at the recorder can apply it at the step provenance already attributes.

**The randomiser probe is named, not excluded by a syntactic class.** It is the one entry the
first query can file, and the honest reason it is not a target is the frame it was made under
— `HandlerCarrier.not_filesLeft_randomizerInput` — and not that its bytes happen to lie in a
class the narrowing removes. A clause added to a class to keep one query out of a recording is a
provenance fact wearing a syntactic disguise, and it works only while the syntax happens to
separate the two. -/

set_option maxHeartbeats 800000 in
/-- **A rejected request files nothing**, because it makes no query. -/
theorem sign_right_record_none (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (sk : SecretKey) (request : Message) (hframe : request.frame = none)
    (state : SplitState) (result : Option Bytes × SplitState)
    (hresult : result ∈ support ((simulateQ (recorder leftKeep rightKeep)
      (Scheme.sign (m := OracleComp OracleWorld) sk request)).run state)) :
    result.2 = state := by
  rw [Scheme.sign, hframe] at hresult
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
  rw [hresult]

set_option maxHeartbeats 800000 in
/-- **A served request files what its `signInternal` files.** -/
theorem sign_right_record (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (sk : SecretKey) (request : Message) (framed : Bytes)
    (hframe : request.frame = some framed)
    (state : SplitState) (result : Option Bytes × SplitState)
    (hresult : result ∈ support ((simulateQ (recorder leftKeep rightKeep)
      (Scheme.sign (m := OracleComp OracleWorld) sk request)).run state)) :
    ∀ entry ∈ result.2.2.2, entry ∈ state.2.2 ∨
      entry.1 = Hashing.randomizerInput sk.prf sk.publicKey.seed framed ∨
      ∃ (mid : QueryCache HashSpec) (answer : HashOutput),
        mid (Hashing.randomizerInput sk.prf sk.publicKey.seed framed) = some answer ∧
          (∀ (probe : Bytes) (value : HashOutput),
            mid probe = some value → result.2.1 probe = some value) ∧
            mid entry.1 = none ∧ rightKeep entry.1 mid := by
  classical
  rw [Scheme.sign, hframe] at hresult
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hresult
  obtain ⟨inner, hinner, hvalue⟩ := hresult
  rw [show result.2 = inner.2 from by rw [hvalue]]
  exact signInternal_right_record leftKeep rightKeep sk framed state inner hinner

end SlhDsaSecurity.SignerRightRecord
