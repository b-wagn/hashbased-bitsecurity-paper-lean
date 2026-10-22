import SlhDsaSecurity.Proof.RecordedTail
import SlhDsaSecurity.Proof.RandomiserRecord
import SlhDsaSecurity.Proof.SignerRandomiser

/-!
# The signer's own queries, as a thing one can instrument

`RecordedTail` records the adversary's hash queries and the verifier's, and deliberately not the
signer's: the signer runs through `liftM` into the base monad, where the recording handler never
sees it. That was right for the randomiser charge, whose record is the adversary's own inputs.
It is wrong for anything that needs to know **which queries the signer made**, and two things now
do — the disclosing list of the coverage split, and any notion of disclosure that wants to be
the signer's own rather than a cache proxy an adversary can forge.

The obstacle is one line of presentation, not of mathematics. `Security.signingOracle` calls
`liftM (Scheme.sign sk request)`, so the signer's sub-run is opaque; the fix is to call it under
its own instrumentation and tell what it recorded. `RecordedQueries.recordedSigningOracle`
already takes the signer as a parameter, so nothing in the game has to move — the sub-run simply
stops being `liftM` of an opaque computation and becomes `liftM` of an instrumented one.

The writer therefore carries **two** records, not one: the adversary's and the verifier's on the
left, the signer's on the right. Keeping them apart is the point. `RecordedTail.card_eq_work`
says the left one is exactly `Outcome.counts.work`, and that stays true because the signer's
hashes are charged to neither counter — `signerCost` charges nothing and records everything.

`map_splitAfterSeeds` is the same invisibility `RecordedQueries.map_recordedAfterSeeds` proves:
forgetting both records returns `WarmedGame.afterSeeds` exactly, so no probability moves.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.SplitRecorder

open Security RecordedQueries

/-! ## A recording run returns the run it records

`countRecorded` wraps a computation with a cost writer and hands back the pair. Dropping the
tally returns the computation itself — which is what makes an instrumented signer substitutable
for the real one inside a signing oracle. -/

theorem countRecorded_fst {α : Type} (cost : OracleWorld.Domain → Tally)
    (computation : OracleComp OracleWorld α) :
    Prod.fst <$> countRecorded cost computation = computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => rw [countRecorded_pure]; simp
  | query_bind queried next ih =>
    rw [countRecorded_query_bind, map_bind]
    refine congrArg (Bind.bind _) (funext fun answer => ?_)
    rw [Functor.map_map]
    simpa only [Function.comp_def] using ih answer

/-- **A recorded sub-run may be substituted for the run it records.** -/
theorem bind_countRecorded {α β : Type} (cost : OracleWorld.Domain → Tally)
    (computation : OracleComp OracleWorld α) (next : α → OracleComp OracleWorld β) :
    countRecorded cost computation >>= (fun step => next step.1) = computation >>= next := by
  conv_rhs => rw [← countRecorded_fst cost computation]
  rw [map_eq_bind_pure_comp, bind_assoc]
  simp [Function.comp_def]

/-! ## The two records

The signer's queries are charged to no counter — `Outcome.counts` counts signing *requests*, not
the signer's hashing — so the cost that records them has a zero `Counts` component. That is what
keeps `RecordedTail.card_eq_work` true of the other record. -/

/-- The counters, the adversary's and the verifier's record, and the signer's. -/
abbrev Split := Counts × Multiset Bytes × Multiset Bytes

/-- What the signer's instrumentation charges: nothing, and records its input. -/
def signerCost : OracleWorld.Domain → Tally := fun input => (0, recordOf input)

/-- The projection that forgets both records. -/
def forgetBoth : Multiplicative Split → Multiplicative Counts :=
  fun tally => Multiplicative.ofAdd (Multiplicative.toAdd tally).1

theorem forgetBoth_one : forgetBoth 1 = 1 := rfl

theorem forgetBoth_mul (left right : Multiplicative Split) :
    forgetBoth (left * right) = forgetBoth left * forgetBoth right := rfl

/-- The projection that keeps the adversary's record and forgets the signer's. -/
def narrow : Multiplicative Split → Multiplicative Tally :=
  fun tally =>
    Multiplicative.ofAdd ((Multiplicative.toAdd tally).1, (Multiplicative.toAdd tally).2.1)

theorem narrow_one : narrow 1 = 1 := rfl

theorem narrow_mul (left right : Multiplicative Split) :
    narrow (left * right) = narrow left * narrow right := rfl

theorem forget_narrow (tally : Multiplicative Split) :
    RecordedQueries.forget (narrow tally) = forgetBoth tally := rfl

/-! ## The two handlers

The adversary's is `RecordedQueries.recordedAdversaryImpl` at the wider writer; the signer's runs
`Scheme.sign` under its own instrumentation and tells what it recorded. -/

/-- The run both handlers live in. -/
abbrev SplitRun := AddWriterT Split (StateT SigningLog (OracleComp OracleWorld))

/-- The adversary's own handler: charge the call, record its input, record nothing for the
signer. -/
noncomputable def splitAdversaryImpl : QueryImpl OracleWorld SplitRun :=
  (QueryImpl.ofLift OracleWorld (StateT SigningLog (OracleComp OracleWorld))).withAddCost
    fun input => ((Counts.single .hash (hashCost input), recordOf input, 0) : Split)

theorem run_splitAdversaryImpl_map (queried : OracleWorld.Domain) :
    (recordedAdversaryImpl queried).run =
      (fun step => (step.1, narrow step.2)) <$> (splitAdversaryImpl queried).run :=
  run_withAddCost_map narrow
    (QueryImpl.ofLift OracleWorld (StateT SigningLog (OracleComp OracleWorld)))
    (fun input => ((Counts.single .hash (hashCost input), recordOf input, 0) : Split))
    (fun input => ((Counts.single .hash (hashCost input), recordOf input) : Tally))
    (fun _ => rfl) queried

theorem run_splitAdversaryImpl_forget (queried : OracleWorld.Domain) :
    (((QueryImpl.ofLift OracleWorld (StateT SigningLog (OracleComp OracleWorld))).withAddCost
        fun input => Counts.single .hash (hashCost input)) queried).run =
      (fun step => (step.1, forgetBoth step.2)) <$> (splitAdversaryImpl queried).run :=
  run_withAddCost_map forgetBoth
    (QueryImpl.ofLift OracleWorld (StateT SigningLog (OracleComp OracleWorld)))
    (fun input => ((Counts.single .hash (hashCost input), recordOf input, 0) : Split))
    (fun input => Counts.single .hash (hashCost input)) (fun _ => rfl) queried

/-- **The signing oracle with its signer instrumented.** The sub-run is `Scheme.sign` under its
own recorder, so what the signer asked is a value the oracle can tell — which is the whole point
of the presentation. -/
noncomputable def splitSigningOracle (sk : SecretKey) : QueryImpl SigningSpec SplitRun :=
  fun request => do
    let step ← liftM (countRecorded signerCost (Scheme.sign sk request) :
      OracleComp OracleWorld (Option Bytes × Tally))
    AddWriterT.addTell ((Counts.single .signing 1, 0, step.2.2) : Split)
    liftM (modify (fun signed => signed ++ [⟨request, step.1⟩]) :
      StateT SigningLog (OracleComp OracleWorld) Unit)
    return step.1

theorem run_splitSigningOracle (sk : SecretKey) (request : Message) (log : SigningLog) :
    ((splitSigningOracle sk request).run).run log =
      countRecorded signerCost (Scheme.sign sk request) >>= fun step =>
        (pure ((step.1, Multiplicative.ofAdd
            ((Counts.single .signing 1 : Counts), (0 : Multiset Bytes), step.2.2)),
          log ++ [⟨request, step.1⟩]) :
          OracleComp OracleWorld ((Option Bytes × Multiplicative Split) × SigningLog)) := by
  simp only [splitSigningOracle, WriterT.run_bind, WriterT.run_pure, AddWriterT.run_addTell,
    StateT.run_bind, StateT.run_pure, run_liftM_base, run_liftM_inner, StateT.run_modify,
    map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, one_mul, mul_one]

/-- **Forgetting both records turns the instrumented signing oracle back into the game's.** -/
theorem run_splitSigningOracle_map (sk : SecretKey) (request : Message) :
    (StrippedGame.signingOracleWith (Scheme.sign sk) request).run =
      (fun step => (step.1, forgetBoth step.2)) <$> (splitSigningOracle sk request).run := by
  funext log
  show ((StrippedGame.signingOracleWith (Scheme.sign sk) request).run).run log =
    (fun step : (Option Bytes × Multiplicative Split) × SigningLog =>
      ((step.1.1, forgetBoth step.1.2), step.2)) <$>
        ((splitSigningOracle sk request).run).run log
  rw [StrippedGame.run_signingOracleWith, run_splitSigningOracle, map_eq_bind_pure_comp,
    bind_assoc]
  simp only [Function.comp_def, pure_bind]
  exact (bind_countRecorded signerCost (Scheme.sign sk request)
    (fun answer => (pure (((answer, Multiplicative.ofAdd (Counts.single .signing 1)),
      log ++ [⟨request, answer⟩]) :
        (Option Bytes × Multiplicative Counts) × SigningLog)))).symm


/-! ## The game, with both phases recorded

The verifier's record joins the adversary's, as in `RecordedTail` — they are the two the counters
charge, and keeping them together is what keeps `RecordedTail.card_eq_work` meaningful. The
signer's is the new component and stands alone. -/

/-- `WarmedGame.afterSeeds` with the adversary's and the verifier's queries recorded on the left
and the signer's on the right. -/
noncomputable def splitAfterSeeds (adversary : Adversary) (sds : Digest × Digest × Digest) :
    OracleComp OracleWorld (Outcome × Multiset Bytes × Multiset Bytes) := do
  let (sk, pk) ← Scheme.keygenInternal sds.1 sds.2.1 sds.2.2
  let ((forgery, tally), signed) ←
    (simulateQ (splitAdversaryImpl + splitSigningOracle sk) (adversary.main pk)).run.run []
  let (verified, verifierTally) ← countRecorded verifierCost
    (Scheme.verify pk forgery.message forgery.signature)
  return ({
    forgery := forgery
    signed := signed
    verified := verified
    counts := (Multiplicative.toAdd tally).1 + verifierTally.1 },
    (Multiplicative.toAdd tally).2.1 + verifierTally.2,
    (Multiplicative.toAdd tally).2.2)

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 1000000 in
/-- **Both recordings are invisible.** Forgetting them returns the game exactly, so instrumenting
the signer's sub-run costs no probability. -/
theorem map_splitAfterSeeds (adversary : Adversary) (sds : Digest × Digest × Digest) :
    Prod.fst <$> splitAfterSeeds adversary sds = WarmedGame.afterSeeds adversary sds := by
  unfold splitAfterSeeds WarmedGame.afterSeeds
  rw [map_bind]
  refine congrArg (Bind.bind _) (funext fun keys => ?_)
  obtain ⟨sk, pk⟩ := keys
  dsimp only
  rw [map_bind,
    show ((simulateQ
        (((QueryImpl.ofLift OracleWorld (StateT SigningLog (OracleComp OracleWorld))).withAddCost
            fun input => Counts.single QueryKind.hash (hashCost input)) +
          Security.signingOracle sk) (adversary.main pk)).run).run [] =
      (fun step => ((step.1.1, forgetBoth step.1.2), step.2)) <$>
        ((simulateQ (splitAdversaryImpl + splitSigningOracle sk)
          (adversary.main pk)).run).run [] from by
      rw [run_simulateQ_map_writer forgetBoth forgetBoth_one forgetBoth_mul
        (splitAdversaryImpl + splitSigningOracle sk)
        (((QueryImpl.ofLift OracleWorld (StateT SigningLog (OracleComp OracleWorld))).withAddCost
            fun input => Counts.single QueryKind.hash (hashCost input)) +
          Security.signingOracle sk)
        (fun t => by
          rcases t with world | request
          · exact run_splitAdversaryImpl_forget world
          · exact run_splitSigningOracle_map sk request) (adversary.main pk)]
      exact stateT_map_apply _ _ [],
    bind_map_left]
  refine congrArg (Bind.bind _) (funext fun advStep => ?_)
  obtain ⟨⟨forgery, tally⟩, signed⟩ := advStep
  dsimp only
  rw [map_bind, countQueries_verification_eq, bind_map_left]
  refine congrArg (Bind.bind _) (funext fun verifyStep => ?_)
  obtain ⟨verified, verifierTally⟩ := verifyStep
  rfl

/-! ## The tail at this presentation -/

/-- The counted game played from what the walk left, with both records. -/
noncomputable def splitTail (adversary : Adversary)
    (start : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec) :
    ProbComp (((Outcome × Multiset Bytes × Multiset Bytes) × Nat) × QueryCache HashSpec) :=
  (simulateQ KeygenUniform.rom
    (countAllHashes (splitAfterSeeds adversary start.1.1))).run start.2

/-- **The warmed tail is this presentation with both records dropped.** -/
theorem tail_eq_map_splitTail (adversary : Adversary)
    (start : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec) :
    WarmedGame.tail adversary start =
      (fun result => ((result.1.1.1, result.1.2), result.2)) <$>
        splitTail adversary start := by
  rw [WarmedGame.tail, splitTail, ← map_splitAfterSeeds adversary start.1.1,
    RecordedTail.countAllHashes_map, simulateQ_map, StateT.run_map]

/-- **So any event about the tail may be read at this presentation.** -/
theorem probEvent_tail_eq (adversary : Adversary)
    (start : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec)
    (event : (Outcome × Nat) × QueryCache HashSpec → Prop) :
    Pr[event | WarmedGame.tail adversary start] =
      Pr[fun result => event ((result.1.1.1, result.1.2), result.2) |
        splitTail adversary start] := by
  rw [tail_eq_map_splitTail, probEvent_map]
  rfl

/-! ## What the signer's record holds, by construction

The point of the presentation: the signer's own queries are a value of the run, so a statement
about what the signer asked needs no test on the cache and no provenance argument. The first of
them is its `PRF_msg` query, which is the one `CacheAvailability.SignerRandomised` is keyed on —
so "the signer produced a signature for this request" becomes readable from the record rather
than guessed at from an entry an adversary could equally have made. -/

/-- **A served request's own `PRF_msg` input is in the signer's record.** -/
theorem mem_signerRecord_randomizer (sk : SecretKey) (request : Message) (framed : Bytes)
    (hframe : request.frame = some framed) (cache : QueryCache HashSpec)
    (step : (Option Bytes × Tally) × QueryCache HashSpec)
    (hstep : step ∈ support ((simulateQ KeygenUniform.rom
      (countRecorded signerCost
        (Scheme.sign (m := OracleComp OracleWorld) sk request))).run cache)) :
    Hashing.randomizerInput sk.prf sk.publicKey.seed framed ∈ step.1.2.2 := by
  have hshape : Scheme.sign (m := OracleComp OracleWorld) sk request =
      (query (spec := OracleWorld)
          (Sum.inr (Hashing.randomizerInput sk.prf sk.publicKey.seed framed)) :
        OracleComp OracleWorld HashOutput) >>= fun answer =>
          (SignerRandomiser.signInternalAt (Hashing.truncate answer) sk framed >>=
            fun signature => pure (some signature.toBytes)) := by
    simp only [Scheme.sign, hframe]
    rw [SignerRandomiser.signInternal_eq]
    rfl
  rw [hshape] at hstep
  exact RandomiserRecord.mem_record_head signerCost _ _ cache step hstep _
    (by simp [signerCost, recordOf])

end SlhDsaSecurity.SplitRecorder
