import SlhDsaSecurity.Proof.CarrierSignRecord
import SlhDsaSecurity.Proof.CarrierTail

/-!
# Where a target-recorded entry of the bracketed phase came from

`PhaseRightRecord.right_record_phase` at the handler the obligations are moving to, and over the
**bracketed** fusion rather than the plain one. Two differences, both of which make it smaller.

The brackets are not a case. `BracketedRun.Bracket` says they touch neither the cache nor either
recording, so a bracketed signing step files exactly what its sub-run files.

And the signing step is one application of `CarrierSignRecord.sign_right_record`, which already
says what a served request can file: its own randomiser probe, or an entry whose carrier already
held that request's randomiser answer.

**The record arithmetic is the one thing that differs in kind.** A phase threads its writer
through the *state*, so a step's own record is a factor of the final accumulator rather than a
summand of a returned value, and the membership is recovered through
`RecordInvariant.fuseServing_accumulates` rather than by splitting a product the value carries.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.CarrierPhaseRecord

open Security BracketedRun CarrierFiles CarrierRecordings CarrierSignRecord CarriedWitness
  PhaseFusion RecordedQueries RecordInvariant

variable (pk : PublicKey)

/-! ## The adversary's own step -/

set_option maxHeartbeats 1000000 in
/-- **A hash step of the adversary's files at most its own input, and that input is what it
records.** -/
theorem right_record_adversaryImpl (rightKeep : Bytes → HandlerCarrier.State → Prop)
    (queried : OracleWorld.Domain) (log : SigningLog) (carrier : CountedState)
    (outer : ((OracleWorld.Range queried × Multiplicative Tally) × SigningLog) × CountedState)
    (houter : outer ∈ support ((simulateQ (countedCarrierRecorder pk rightKeep)
      (((recordedAdversaryImpl queried).run).run log)).run carrier)) :
    ∀ entry ∈ outer.2.2.1.2, entry ∈ carrier.2.1.2 ∨
      entry.1 ∈ (Multiplicative.toAdd outer.1.1.2).2 := by
  classical
  rw [run_recordedAdversaryImpl, simulateQ_map, StateT.run_map,
    PhaseRightRecord.simulateQ_worldQuery, support_map] at houter
  obtain ⟨step, hstep, heq⟩ := houter
  have hstate : outer.2 = step.2 := by rw [← heq]
  have hrecord : outer.1.1.2 = Multiplicative.ofAdd
      ((Counts.single .hash (hashCost queried) : Counts), recordOf queried) := by rw [← heq]
  intro entry hentry
  rw [hstate] at hentry
  rcases step_right_shape pk rightKeep queried carrier step hstep with
    hsame | ⟨appended, answer, hqueried, hshape, -, -, -⟩
  · rw [hsame] at hentry
    exact Or.inl hentry
  · rw [hshape] at hentry
    rcases List.mem_append.mp hentry with hprior | hself
    · exact Or.inl hprior
    · refine Or.inr ?_
      rw [hrecord, toAdd_ofAdd]
      simp only [List.mem_singleton] at hself
      rw [hself, hqueried]
      show appended ∈ recordOf (Sum.inr appended)
      simp [recordOf]

/-! ## The attribution -/

/-- Where a target-recorded entry of the phase can have come from: the adversary's own record,
or a signing sub-run — and in the second case, either the request's randomiser probe or an entry
filed at a carrier that already held that request's randomiser answer. -/
def CarrierRightSource (sk : SecretKey) (rightKeep : Bytes → HandlerCarrier.State → Prop)
    (record : Multiset Bytes) (final : QueryCache HashSpec) (entry : Bytes × HashOutput) :
    Prop :=
  entry.1 ∈ record ∨
    ∃ framed : Bytes,
      entry.1 = Hashing.randomizerInput sk.prf sk.publicKey.seed framed ∨
        ∃ (mid : HandlerCarrier.State) (answer : HashOutput),
          mid.cache (Hashing.randomizerInput sk.prf sk.publicKey.seed framed) = some answer ∧
            (∀ (probe : Bytes) (value : HashOutput),
              mid.cache probe = some value → final probe = some value) ∧
              mid.cache entry.1 = none ∧
                rightKeep entry.1 (servingNotice pk mid entry.1) ∧
                  mid.framing = some framed ∧
                    CacheReplay.QueriesUnder final
                      (SignerRandomiser.signInternalAt (m := OracleComp HashSpec)
                        (Hashing.truncate answer) sk framed) entry.1

theorem CarrierRightSource.mono {sk : SecretKey}
    {rightKeep : Bytes → HandlerCarrier.State → Prop} {record wider : Multiset Bytes}
    {final : QueryCache HashSpec} {entry : Bytes × HashOutput}
    (hle : record ≤ wider)
    (hsource : CarrierRightSource pk sk rightKeep record final entry) :
    CarrierRightSource pk sk rightKeep wider final entry := by
  rcases hsource with hmem | hsigner
  · exact Or.inl (Multiset.mem_of_le hle hmem)
  · exact Or.inr hsigner

set_option maxHeartbeats 1000000 in
/-- **Every entry the bracketed phase files as a target is the adversary's own query, or a
signing sub-run's.** -/
theorem right_record_phase (rightKeep : Bytes → HandlerCarrier.State → Prop) (sk : SecretKey)
    {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (accumulated : Multiplicative Tally) (log : SigningLog) (carrier : CountedState)
      (result : α × (Multiplicative Tally × SigningLog × CountedState)),
      result ∈ support ((simulateQ (fuseServing (countedCarrierRecorder pk rightKeep)
        (recordedAdversaryImpl + recordedSigningOracle (Scheme.sign sk))
        ServedAgreement.startServingOn ServedAgreement.stopServingOn) computation).run
          (accumulated, log, carrier)) →
      ∀ final : QueryCache HashSpec,
        (∀ (probe : Bytes) (value : HashOutput),
          result.2.2.2.1.cache probe = some value → final probe = some value) →
        ∀ entry ∈ result.2.2.2.2.1.2, entry ∈ carrier.2.1.2 ∨
          CarrierRightSource pk sk rightKeep (Multiplicative.toAdd result.2.1).2 final entry := by
  classical
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro accumulated log carrier result hresult final hfinal entry hentry
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
    rw [show result.2.2.2 = carrier from by rw [hresult]] at hentry
    exact Or.inl hentry
  | query_bind queried next ih =>
    intro accumulated log carrier result hresult final hfinal entry hentry
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hresult
    obtain ⟨step, hstep, hrest⟩ := hresult
    -- The accumulator only gains factors, so a step's own record is inside the phase's.
    obtain ⟨gained, hgained⟩ := fuseServing_accumulates (countedCarrierRecorder pk rightKeep)
      _ _ _ (next step.1) step.2 result hrest
    have hle : (Multiplicative.toAdd step.2.1).2 ≤ (Multiplicative.toAdd result.2.1).2 := by
      rw [hgained, toAdd_mul]
      exact Multiset.le_add_right _ _
    rcases ih step.1 step.2.1 step.2.2.1 step.2.2.2 result hrest final hfinal entry hentry with
      hstepMem | hsource
    · rcases queried with world | request
      · -- The adversary's own query.
        have hstep' : step ∈ support
            ((simulateQ (countedCarrierRecorder pk rightKeep)
              (((recordedAdversaryImpl world).run).run log)).run carrier >>= fun z =>
              (pure (z.1.1.1, (accumulated * z.1.1.2, z.1.2, z.2)) :
                ProbComp ((OracleWorld + SigningSpec).Range (Sum.inl world) ×
                  (Multiplicative Tally × SigningLog × CountedState)))) := hstep
        obtain ⟨z, hz, hpure⟩ := support_bind_exists hstep'
        have hzstate : step.2.2.2 = z.2 := congrArg (fun p => p.2.2.2) hpure
        have hztally : step.2.1 = accumulated * z.1.1.2 := congrArg (fun p => p.2.1) hpure
        rw [hzstate] at hstepMem
        rcases right_record_adversaryImpl pk rightKeep world log carrier z hz entry
          hstepMem with hprior | hrec
        · exact Or.inl hprior
        · refine Or.inr (Or.inl (Multiset.mem_of_le hle ?_))
          rw [hztally, toAdd_mul]
          exact Multiset.mem_add.mpr (Or.inr hrec)
      · -- A signing request: the brackets touch neither recording, so its sub-run files it.
        have hstep' : step ∈ support
            ((simulateQ (countedCarrierRecorder pk rightKeep)
                (((recordedSigningOracle (Scheme.sign sk) request).run).run log)).run
              (ServedAgreement.startServingOn request carrier) >>= fun z =>
              (pure (z.1.1.1, (accumulated * z.1.1.2, z.1.2,
                  ServedAgreement.stopServingOn z.2)) :
                ProbComp ((OracleWorld + SigningSpec).Range (Sum.inr request) ×
                  (Multiplicative Tally × SigningLog × CountedState)))) := hstep
        obtain ⟨z, hz, hpure⟩ := support_bind_exists hstep'
        have hzstate : step.2.2.2 = ServedAgreement.stopServingOn z.2 :=
          congrArg (fun p => p.2.2.2) hpure
        rw [hzstate, (CarrierTail.bracket_stopServingOn z.2).2]
          at hstepMem
        rw [run_recordedSigningOracle, simulateQ_bind, StateT.run_bind] at hz
        obtain ⟨signed, hsigned, hsignedPure⟩ := support_bind_exists hz
        have hsignedState : z.2 = signed.2 := congrArg Prod.snd hsignedPure
        rw [hsignedState] at hstepMem
        have hcarrierFinal : ∀ (probe : Bytes) (value : HashOutput),
            signed.2.1.cache probe = some value → final probe = some value := by
          intro probe value hprobe
          refine hfinal probe value ?_
          have hgrow : ∀ (probe : Bytes) (value : HashOutput),
              step.2.2.2.1.cache probe = some value →
                result.2.2.2.1.cache probe = some value := by
            refine phase_invariant (Inv := fun t : CountedState => ∀ probe value,
                step.2.2.2.1.cache probe = some value → t.1.cache probe = some value)
              (countedCarrierRecorder pk rightKeep) _ _ _ ?_ ?_ ?_ (next step.1)
              step.2.1 step.2.2.1 step.2.2.2 result hrest (fun _ _ h => h)
            · intro q st stp hstp hinv probe' value' hvalue'
              exact ((files_countedCarrierRecorder pk rightKeep).stepGrows q st stp hstp).1
                probe' value' (hinv probe' value' hvalue')
            · intro request' st hinv probe' value' hvalue'
              rw [(CarrierTail.bracket_startServingOn request' st).1]
              exact hinv probe' value' hvalue'
            · intro st hinv probe' value' hvalue'
              rw [(CarrierTail.bracket_stopServingOn st).1]
              exact hinv probe' value' hvalue'
          refine hgrow probe value ?_
          rw [hzstate, (CarrierTail.bracket_stopServingOn z.2).1, hsignedState]
          exact hprobe
        cases hframe : request.frame with
        | none =>
          rw [sign_right_record_none pk rightKeep sk request hframe _ signed hsigned,
            (CarrierTail.bracket_startServingOn request carrier).2]
            at hstepMem
          exact Or.inl hstepMem
        | some framed =>
          rcases sign_right_record pk rightKeep sk request framed hframe _ signed hsigned
            final hcarrierFinal entry hstepMem with
            hprior | hrandomiser | ⟨mid, answer, hmid, hlater, habsent, hkeep, hframing, hqueries⟩
          · rw [(CarrierTail.bracket_startServingOn request carrier).2] at hprior
            exact Or.inl hprior
          · exact Or.inr (Or.inr ⟨framed, Or.inl hrandomiser⟩)
          · refine Or.inr (Or.inr ⟨framed, Or.inr ⟨mid, answer, hmid,
              fun probe value hprobe => hcarrierFinal probe value (hlater probe value hprobe),
              habsent, hkeep, ?_, hqueries⟩⟩)
            rw [hframing, ServedAgreement.startServingOn, hframe]
            rfl
    · exact Or.inr hsource

end SlhDsaSecurity.CarrierPhaseRecord
