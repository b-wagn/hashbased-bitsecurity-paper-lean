import XmssSecurity.Proof.Common.Modes.QueryKinds
import XmssSecurity.Proof.Common.Modes.AllHashes

/-!
# Repeated epochs

The experiments of the statement answer a request for an epoch that was already signed by `⊥`,
without running the signer. The proofs were written for the variant of `LossyGames.lean`, in
which the signing oracle answers every request and a transcript with two requests for the same
epoch makes the forgery lose. This file transfers bit security from the lossy games to the
statement's games:

* security (`hasClassicalSecurityBits_of_lossy`): an adversary of the statement's game is
  simulated, with the same winning probability and at most the same counts, by the adversary
  `filtered` of the lossy game that answers its repeated requests itself, by `⊥`;
* attacks (`advantage_eq_lossy`, `hasQueryBound_iff_lossy`): an adversary that makes at most one
  signing request (`OneRequest`) has the same experiment in both games.
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.SUFCMA

variable {ι : Type} {spec : OracleSpec ι} {PK SK Msg Sig : Type} {L : ℕ}

/-- A query to the signing oracle. -/
def IsSigningQuery : (spec + SigningSpec Msg Sig L).Domain → Prop
  | .inl _ => False
  | .inr _ => True

instance : DecidablePred (IsSigningQuery (spec := spec) (Msg := Msg) (Sig := Sig) (L := L)) :=
  fun input => by cases input <;> unfold IsSigningQuery <;> infer_instance

/-- The adversary makes at most one signing request. -/
def OneRequest (adversary : Adversary spec PK Msg Sig L) : Prop :=
  ∀ pk, (adversary.main pk).IsQueryBoundP (IsSigningQuery (spec := spec) (Msg := Msg) (Sig := Sig))
    1

section Runs

variable (cost : spec.Domain → ℕ) (scheme : EpochBasedSignature spec PK SK Msg Sig L) (sk : SK)

/-- The oracles of the statement's experiment. -/
abbrev paperImpl :
    QueryImpl (spec + SigningSpec Msg Sig L) (CountedRun spec Msg Sig L) :=
  (QueryImpl.ofLift spec (StateT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec))).withAddCost
      (fun t => QueryCounts.single .hash (cost t)) +
    countedSigningOracle cost scheme sk

/-- The oracles of the lossy experiment. -/
abbrev lossyImpl :
    QueryImpl (spec + SigningSpec Msg Sig L) (LossyRun spec Msg Sig L) :=
  (QueryImpl.ofLift spec (WriterT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec))).withAddCost
      (fun t => QueryCounts.single .hash (cost t)) +
    lossySigningOracle cost scheme sk

variable {cost scheme sk}

theorem paperRun_query_bind {α : Type} (input : (spec + SigningSpec Msg Sig L).Domain)
    (next : (spec + SigningSpec Msg Sig L).Range input → OracleComp (spec + SigningSpec Msg Sig L) α)
    (signed : QueryLog (SigningSpec Msg Sig L)) :
    (simulateQ (paperImpl cost scheme sk)
        (liftM ((spec + SigningSpec Msg Sig L).query input) >>= next)).run.run signed =
      (paperImpl cost scheme sk input).run.run signed >>= fun p =>
        (fun q => ((q.1.1, p.1.2 * q.1.2), q.2)) <$>
          (simulateQ (paperImpl cost scheme sk) (next p.1.1)).run.run p.2 := by
  simp [simulateQ_bind, WriterT.run_bind, StateT.run_bind]

theorem lossyRun_query_bind {α : Type} (input : (spec + SigningSpec Msg Sig L).Domain)
    (next : (spec + SigningSpec Msg Sig L).Range input → OracleComp (spec + SigningSpec Msg Sig L) α) :
    (simulateQ (lossyImpl cost scheme sk)
        (liftM ((spec + SigningSpec Msg Sig L).query input) >>= next)).run.run =
      (lossyImpl cost scheme sk input).run.run >>= fun p =>
        (fun q => ((q.1.1, p.1.2 * q.1.2), p.2 ++ q.2)) <$>
          (simulateQ (lossyImpl cost scheme sk) (next p.1.1)).run.run := by
  simp [simulateQ_bind, WriterT.run_bind]

theorem paperImpl_hash (t : spec.Domain) (signed : QueryLog (SigningSpec Msg Sig L)) :
    (paperImpl cost scheme sk (.inl t)).run.run signed =
      (fun a => ((a, Multiplicative.ofAdd (QueryCounts.single .hash (cost t))), signed)) <$>
        (liftM (spec.query t) :
          OracleComp spec ((spec + SigningSpec Msg Sig L).Range (.inl t))) := by
  simp [QueryImpl.withAddCost_apply, AddWriterT.addTell]

theorem lossyImpl_hash (t : spec.Domain) :
    (lossyImpl cost scheme sk (.inl t)).run.run =
      (fun a => ((a, Multiplicative.ofAdd (QueryCounts.single .hash (cost t))), [])) <$>
        (liftM (spec.query t) :
          OracleComp spec ((spec + SigningSpec Msg Sig L).Range (.inl t))) := by
  simp only [QueryImpl.add_apply_inl, QueryImpl.withAddCost_apply, QueryImpl.ofLift_apply,
    WriterT.run_bind, WriterT.run_map, AddWriterT.run_addTell, Modes.run_liftM_of_liftM,
    Modes.run_liftM_of_liftM', pure_bind, Functor.map_map, map_bind, mul_one]
  rfl

theorem paperRun_liftM {α : Type} (x : OracleComp spec α) (signed : QueryLog (SigningSpec Msg Sig L)) :
    ((liftM x : CountedRun spec Msg Sig L α).run).run signed =
      (fun a => ((a, 1), signed)) <$> x := by
  show ((fun a => (a, (1 : Multiplicative QueryCounts))) <$>
    (liftM x : StateT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec) α)).run signed = _
  simp

theorem paperRun_get (signed : QueryLog (SigningSpec Msg Sig L)) :
    ((liftM (get : StateT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec) _) :
      CountedRun spec Msg Sig L _).run).run signed = pure ((signed, 1), signed) := by
  show ((fun a => (a, (1 : Multiplicative QueryCounts))) <$>
    (get : StateT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec) _)).run signed = _
  simp

theorem paperRun_set (signed signed' : QueryLog (SigningSpec Msg Sig L)) :
    ((liftM (set signed' : StateT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec) PUnit) :
      CountedRun spec Msg Sig L PUnit).run).run signed = pure ((⟨⟩, 1), signed') := by
  show ((fun a => (a, (1 : Multiplicative QueryCounts))) <$>
    (set signed' : StateT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec) PUnit)).run signed = _
  simp

theorem paperRun_addTell (w : QueryCounts) (signed : QueryLog (SigningSpec Msg Sig L)) :
    ((AddWriterT.addTell (M := StateT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec)) w).run).run
      signed = pure ((⟨⟩, Multiplicative.ofAdd w), signed) := by
  simp [AddWriterT.run_addTell]

theorem lossyRun_liftM {α : Type} (x : OracleComp spec α) :
    ((liftM x : LossyRun spec Msg Sig L α).run).run = (fun a => ((a, 1), [])) <$> x := by
  show ((fun a => (a, (1 : Multiplicative QueryCounts))) <$>
    (liftM x : WriterT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec) α)).run = _
  rw [WriterT.run_map', Modes.run_liftM_of_liftM']
  simp [Functor.map_map]

theorem paperImpl_sign_signed (request : SignRequest Msg L)
    (signed : QueryLog (SigningSpec Msg Sig L))
    (hsigned : SigningTranscript.Signed signed request.epoch = true) :
    (paperImpl cost scheme sk (.inr request)).run.run signed =
      pure (f := OracleComp spec)
        (α := ((spec + SigningSpec Msg Sig L).Range (.inr request) × Multiplicative QueryCounts) ×
          QueryLog (SigningSpec Msg Sig L))
        ((none, Multiplicative.ofAdd (QueryCounts.single .sign 1)), signed) := by
  show (countedSigningOracle cost scheme sk request).run.run signed = _
  unfold countedSigningOracle
  simp only [WriterT.run_bind, StateT.run_bind, StateT.run_map, paperRun_addTell, paperRun_get,
    pure_bind, map_pure, hsigned, if_true, WriterT.run_pure, StateT.run_pure]
  simp

theorem paperImpl_sign_fresh (request : SignRequest Msg L)
    (signed : QueryLog (SigningSpec Msg Sig L))
    (hsigned : SigningTranscript.Signed signed request.epoch = false) :
    (paperImpl cost scheme sk (.inr request)).run.run signed =
      Functor.map (f := OracleComp spec)
        (β := ((spec + SigningSpec Msg Sig L).Range (.inr request) × Multiplicative QueryCounts) ×
          QueryLog (SigningSpec Msg Sig L))
        (fun p => ((p.1, Multiplicative.ofAdd (QueryCounts.single .sign 1 + p.2)),
          signed ++ [⟨request, p.1⟩]))
        (countQueries (fun t => QueryCounts.single .signer (cost t))
          (scheme.sign sk request.epoch request.message)) := by
  show (countedSigningOracle cost scheme sk request).run.run signed = _
  unfold countedSigningOracle
  simp only [WriterT.run_bind, StateT.run_bind, StateT.run_map, paperRun_addTell, paperRun_get,
    pure_bind, map_pure, hsigned, Bool.false_eq_true, if_false, paperRun_liftM, paperRun_set,
    WriterT.run_pure, StateT.run_pure, map_bind, bind_map_left, Functor.map_map]
  simp [ofAdd_add, mul_comm, mul_left_comm]

theorem lossyImpl_sign (request : SignRequest Msg L) :
    (lossyImpl cost scheme sk (.inr request)).run.run =
      Functor.map (f := OracleComp spec)
        (β := ((spec + SigningSpec Msg Sig L).Range (.inr request) × Multiplicative QueryCounts) ×
          QueryLog (SigningSpec Msg Sig L))
        (fun p => ((p.1, Multiplicative.ofAdd (QueryCounts.single .sign 1 + p.2)),
          [⟨request, p.1⟩]))
        (countQueries (fun t => QueryCounts.single .signer (cost t))
          (scheme.sign sk request.epoch request.message)) := by
  show (lossySigningOracle cost scheme sk request).run.run = _
  unfold lossySigningOracle
  simp [WriterT.run_bind, lossyRun_liftM, AddWriterT.run_addTell, map_bind, bind_map_left]

/-! ### Adversaries with at most one request -/

/-- Without signing requests, the statement's oracles and the lossy oracles agree; the table
`Signed` stays as it was. -/
theorem paperRun_eq_lossyRun_of_noRequest {α : Type}
    (computation : OracleComp (spec + SigningSpec Msg Sig L) α)
    (hbound : computation.IsQueryBoundP (IsSigningQuery (spec := spec) (Msg := Msg) (Sig := Sig))
      0)
    (signed : QueryLog (SigningSpec Msg Sig L)) :
    (simulateQ (paperImpl cost scheme sk) computation).run.run signed =
      (fun z => (z.1, signed ++ z.2)) <$> (simulateQ (lossyImpl cost scheme sk) computation).run.run := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      rcases input with t | request
      · have hnext : ∀ answer, (next answer).IsQueryBoundP
            (IsSigningQuery (spec := spec) (Msg := Msg) (Sig := Sig)) 0 := fun answer => by
          simpa [IsSigningQuery] using hbound.2 answer
        rw [paperRun_query_bind, lossyRun_query_bind, paperImpl_hash, lossyImpl_hash]
        simp only [bind_map_left, map_bind, Functor.map_map]
        congr 1
        funext answer
        rw [ih answer (hnext answer)]
        simp [Functor.map_map]
      · exact absurd hbound.1 (by simp [IsSigningQuery])

/-- From the empty table, an adversary with at most one signing request sees the same oracles in
the statement's experiment and in the lossy one. -/
theorem paperRun_eq_lossyRun_of_oneRequest {α : Type}
    (computation : OracleComp (spec + SigningSpec Msg Sig L) α)
    (hbound : computation.IsQueryBoundP (IsSigningQuery (spec := spec) (Msg := Msg) (Sig := Sig))
      1) :
    (simulateQ (paperImpl cost scheme sk) computation).run.run [] =
      (simulateQ (lossyImpl cost scheme sk) computation).run.run := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      rcases input with t | request
      · have hnext : ∀ answer, (next answer).IsQueryBoundP
            (IsSigningQuery (spec := spec) (Msg := Msg) (Sig := Sig)) 1 := fun answer => by
          simpa [IsSigningQuery] using hbound.2 answer
        rw [paperRun_query_bind, lossyRun_query_bind, paperImpl_hash, lossyImpl_hash]
        simp only [bind_map_left, map_bind, Functor.map_map]
        congr 1
        funext answer
        rw [ih answer (hnext answer)]
        simp
      · have hnext : ∀ answer, (next answer).IsQueryBoundP
            (IsSigningQuery (spec := spec) (Msg := Msg) (Sig := Sig)) 0 := fun answer => by
          simpa [IsSigningQuery] using hbound.2 answer
        rw [paperRun_query_bind, lossyRun_query_bind,
          paperImpl_sign_fresh request [] (by simp [SigningTranscript.Signed]), lossyImpl_sign]
        simp only [bind_map_left, map_bind, Functor.map_map]
        congr 1
        funext answer
        rw [paperRun_eq_lossyRun_of_noRequest _ (hnext _)]
        simp [Functor.map_map]

/-! ### Writers over state -/

section WriterState

variable {σ ω : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Monoid ω]

theorem writerState_run_liftM {α : Type} (x : StateT σ m α) (state : σ) :
    ((liftM x : WriterT ω (StateT σ m) α).run).run state =
      (fun p => ((p.1, 1), p.2)) <$> x.run state := by
  show ((fun a => (a, (1 : ω))) <$> x).run state = _
  simp

theorem writerState_run_get (state : σ) :
    ((liftM (get : StateT σ m σ) : WriterT ω (StateT σ m) σ).run).run state =
      pure ((state, 1), state) := by
  rw [writerState_run_liftM]
  simp

theorem writerState_run_set (state state' : σ) :
    ((liftM (set state' : StateT σ m PUnit) : WriterT ω (StateT σ m) PUnit).run).run state =
      pure ((⟨⟩, 1), state') := by
  rw [writerState_run_liftM]
  simp

theorem writerState_run_lift {n : Type → Type} [MonadLiftT n m] {α : Type} (x : n α)
    (state : σ) :
    ((liftM x : WriterT ω (StateT σ m) α).run).run state =
      (fun a => ((a, 1), state)) <$> (liftM x : m α) := by
  show ((fun a => (a, (1 : ω))) <$> (liftM (liftM x : m α) : StateT σ m α)).run state = _
  simp

end WriterState

/-! ### Filtering repeated requests -/

/-- The adversary's run in `filtered`: the number of repeated requests, the epochs requested so
far, and the oracles of the lossy experiment. -/
abbrev FilterRun (spec : OracleSpec ι) (Msg Sig : Type) (L : ℕ) : Type → Type :=
  AddWriterT ℕ (StateT (List (Fin L)) (OracleComp (spec + SigningSpec Msg Sig L)))

variable (spec Msg Sig L) in
/-- Forward every query, except a signing request for an epoch requested before, which is
answered by `⊥` without a query and counted. -/
def filterImpl : QueryImpl (spec + SigningSpec Msg Sig L) (FilterRun spec Msg Sig L) :=
  fun input => match input with
  | .inl t => liftM ((spec + SigningSpec Msg Sig L).query (.inl t))
  | .inr request => do
      let seen ← liftM (get : StateT (List (Fin L)) (OracleComp (spec + SigningSpec Msg Sig L)) _)
      if request.epoch ∈ seen then
        AddWriterT.addTell (M := StateT (List (Fin L)) (OracleComp (spec + SigningSpec Msg Sig L)))
          1
        return none
      else
        liftM (set (seen ++ [request.epoch]) :
          StateT (List (Fin L)) (OracleComp (spec + SigningSpec Msg Sig L)) PUnit)
        liftM ((spec + SigningSpec Msg Sig L).query (.inr request))

/-- The adversary that answers its own repeated requests by `⊥`. It never requests an epoch
twice. -/
def filtered (adversary : Adversary spec PK Msg Sig L) : Adversary spec PK Msg Sig L :=
  ⟨fun pk => (fun result => result.1.1) <$>
    (simulateQ (filterImpl spec Msg Sig L) (adversary.main pk)).run.run []⟩

theorem filterRun_query_bind {α : Type} (input : (spec + SigningSpec Msg Sig L).Domain)
    (next : (spec + SigningSpec Msg Sig L).Range input → OracleComp (spec + SigningSpec Msg Sig L) α)
    (seen : List (Fin L)) :
    (simulateQ (filterImpl spec Msg Sig L)
        (liftM ((spec + SigningSpec Msg Sig L).query input) >>= next)).run.run seen =
      (filterImpl spec Msg Sig L input).run.run seen >>= fun p =>
        (fun q => ((q.1.1, p.1.2 * q.1.2), q.2)) <$>
          (simulateQ (filterImpl spec Msg Sig L) (next p.1.1)).run.run p.2 := by
  simp [simulateQ_bind, WriterT.run_bind, StateT.run_bind]

theorem filterImpl_hash (t : spec.Domain) (seen : List (Fin L)) :
    (filterImpl spec Msg Sig L (.inl t)).run.run seen =
      (fun a => ((a, 1), seen)) <$>
        (liftM ((spec + SigningSpec Msg Sig L).query (.inl t)) :
          OracleComp (spec + SigningSpec Msg Sig L) ((spec + SigningSpec Msg Sig L).Range (.inl t))) := by
  show ((fun a => (a, (1 : Multiplicative ℕ))) <$>
    (liftM ((spec + SigningSpec Msg Sig L).query (.inl t)) :
      StateT (List (Fin L)) (OracleComp (spec + SigningSpec Msg Sig L)) _)).run seen = _
  simp

theorem filterImpl_sign_seen (request : SignRequest Msg L) (seen : List (Fin L))
    (hseen : request.epoch ∈ seen) :
    (filterImpl spec Msg Sig L (.inr request)).run.run seen =
      pure (f := OracleComp (spec + SigningSpec Msg Sig L))
        (α := ((spec + SigningSpec Msg Sig L).Range (.inr request) × Multiplicative ℕ) × List (Fin L))
        ((none, Multiplicative.ofAdd 1), seen) := by
  show (do
      let seen ← liftM (get : StateT (List (Fin L)) (OracleComp (spec + SigningSpec Msg Sig L)) _)
      if request.epoch ∈ seen then
        AddWriterT.addTell (M := StateT (List (Fin L)) (OracleComp (spec + SigningSpec Msg Sig L)))
          1
        return none
      else
        liftM (set (seen ++ [request.epoch]) :
          StateT (List (Fin L)) (OracleComp (spec + SigningSpec Msg Sig L)) PUnit)
        liftM ((spec + SigningSpec Msg Sig L).query (.inr request)) :
        FilterRun spec Msg Sig L (Option Sig)).run.run seen = _
  simp only [WriterT.run_bind, StateT.run_bind, StateT.run_map, writerState_run_get, pure_bind,
    hseen, if_true, WriterT.run_map, AddWriterT.run_addTell, StateT.run_pure, map_pure]
  simp

theorem filterImpl_sign_fresh (request : SignRequest Msg L) (seen : List (Fin L))
    (hseen : request.epoch ∉ seen) :
    (filterImpl spec Msg Sig L (.inr request)).run.run seen =
      (fun a => ((a, 1), seen ++ [request.epoch])) <$>
        (liftM ((spec + SigningSpec Msg Sig L).query (.inr request)) :
          OracleComp (spec + SigningSpec Msg Sig L)
            ((spec + SigningSpec Msg Sig L).Range (.inr request))) := by
  show (do
      let seen ← liftM (get : StateT (List (Fin L)) (OracleComp (spec + SigningSpec Msg Sig L)) _)
      if request.epoch ∈ seen then
        AddWriterT.addTell (M := StateT (List (Fin L)) (OracleComp (spec + SigningSpec Msg Sig L)))
          1
        return none
      else
        liftM (set (seen ++ [request.epoch]) :
          StateT (List (Fin L)) (OracleComp (spec + SigningSpec Msg Sig L)) PUnit)
        liftM ((spec + SigningSpec Msg Sig L).query (.inr request)) :
        FilterRun spec Msg Sig L (Option Sig)).run.run seen = _
  simp only [WriterT.run_bind, StateT.run_bind, StateT.run_map, writerState_run_get, pure_bind,
    hseen, if_false, writerState_run_set, writerState_run_lift, map_bind, bind_map_left,
    Functor.map_map]
  simp

theorem writerRun_map {ω : Type} [Monoid ω] {m : Type → Type} [Monad m] {α β : Type} (f : α → β)
    (x : WriterT ω m α) : (f <$> x).run = Prod.map f id <$> x.run := rfl

theorem logRun_map {m : Type → Type} [Monad m] {α β : Type} (f : α → β)
    (x : WriterT (QueryLog (SigningSpec Msg Sig L)) m α) : (f <$> x).run = Prod.map f id <$> x.run :=
  rfl

theorem signed_eq_true_iff (signed : QueryLog (SigningSpec Msg Sig L)) (epoch : Fin L) :
    SigningTranscript.Signed signed epoch = true ↔ epoch ∈ signed.map fun entry => entry.1.epoch := by
  unfold SigningTranscript.Signed
  rw [List.any_eq_true, List.mem_map]
  constructor
  · rintro ⟨entry, hentry, h⟩
    exact ⟨entry, hentry, of_decide_eq_true h⟩
  · rintro ⟨entry, hentry, h⟩
    exact ⟨entry, hentry, decide_eq_true h⟩

theorem queryCounts_single_zero (kind : QueryKind) : QueryCounts.single kind 0 = 0 := by
  simp [QueryCounts.single]

theorem queryCounts_single_add (kind : QueryKind) (a b : ℕ) :
    QueryCounts.single kind (a + b) = QueryCounts.single kind a + QueryCounts.single kind b := by
  simp [QueryCounts.single, Pi.single_add]

/-- The statement's oracles are the lossy oracles behind the filter, up to the count of the
repeated requests, which the statement charges as signing queries. -/
theorem paperRun_eq_filtered {α : Type} (computation : OracleComp (spec + SigningSpec Msg Sig L) α)
    (signed : QueryLog (SigningSpec Msg Sig L)) :
    (simulateQ (paperImpl cost scheme sk) computation).run.run signed =
      (fun z => ((z.1.1.1.1, z.1.2 * Multiplicative.ofAdd
          (QueryCounts.single .sign (Multiplicative.toAdd z.1.1.1.2))), signed ++ z.2)) <$>
        (simulateQ (lossyImpl cost scheme sk)
          ((simulateQ (filterImpl spec Msg Sig L) computation).run.run
            (signed.map fun entry => entry.1.epoch))).run.run := by
  induction computation using OracleComp.inductionOn generalizing signed with
  | pure value => simp [queryCounts_single_zero]
  | query_bind input next ih =>
      rcases input with t | request
      · rw [paperRun_query_bind, paperImpl_hash, filterRun_query_bind, filterImpl_hash]
        simp only [bind_map_left]
        rw [lossyRun_query_bind, lossyImpl_hash]
        simp only [bind_map_left, map_bind, Functor.map_map]
        congr 1
        funext answer
        rw [ih answer signed]
        simp [simulateQ_map, writerRun_map, logRun_map, Functor.map_map, Prod.map, mul_assoc]
      · by_cases hseen : request.epoch ∈ signed.map fun entry => entry.1.epoch
        · rw [paperRun_query_bind, paperImpl_sign_signed request signed
            ((signed_eq_true_iff _ _).2 hseen), filterRun_query_bind,
            filterImpl_sign_seen request _ hseen]
          simp only [pure_bind]
          rw [ih]
          simp [simulateQ_map, writerRun_map, logRun_map, Functor.map_map, Prod.map,
            queryCounts_single_add, ofAdd_add, mul_comm, mul_left_comm]
        · have hsigned : SigningTranscript.Signed signed request.epoch = false := by
            cases h : SigningTranscript.Signed signed request.epoch
            · rfl
            · exact absurd ((signed_eq_true_iff _ _).1 h) hseen
          rw [paperRun_query_bind, paperImpl_sign_fresh request signed hsigned,
            filterRun_query_bind, filterImpl_sign_fresh request _ hseen]
          simp only [bind_map_left]
          rw [lossyRun_query_bind, lossyImpl_sign]
          simp only [bind_map_left, map_bind, Functor.map_map]
          congr 1
          funext answer
          rw [ih]
          simp [simulateQ_map, writerRun_map, logRun_map, Functor.map_map, Prod.map, mul_assoc,
            List.append_assoc]

/-- The table `Signed` of the statement's experiment never holds two entries for one epoch. -/
theorem paperRun_nodup {α : Type} (computation : OracleComp (spec + SigningSpec Msg Sig L) α)
    (signed : QueryLog (SigningSpec Msg Sig L))
    (hsigned : (signed.map fun entry => entry.1.epoch).Nodup) :
    ∀ result ∈ support ((simulateQ (paperImpl cost scheme sk) computation).run.run signed),
      (result.2.map fun entry => entry.1.epoch).Nodup := by
  induction computation using OracleComp.inductionOn generalizing signed with
  | pure value => simpa using hsigned
  | query_bind input next ih =>
      intro result hresult
      rw [paperRun_query_bind, mem_support_bind_iff] at hresult
      obtain ⟨step, hstep, hresult⟩ := hresult
      rw [support_map] at hresult
      obtain ⟨inner, hinner, rfl⟩ := hresult
      rcases input with t | request
      · rw [paperImpl_hash, support_map] at hstep
        obtain ⟨answer, -, rfl⟩ := hstep
        exact ih _ signed hsigned inner hinner
      · cases h : SigningTranscript.Signed signed request.epoch
        · rw [paperImpl_sign_fresh request signed h, support_map] at hstep
          obtain ⟨answer, -, rfl⟩ := hstep
          refine ih _ _ ?_ inner hinner
          have hfresh : request.epoch ∉ signed.map fun entry => entry.1.epoch := fun hmem =>
            absurd ((signed_eq_true_iff _ _).2 hmem) (by simp [h])
          rw [List.map_append, List.nodup_append]
          refine ⟨hsigned, by simp, ?_⟩
          simp only [List.map_cons, List.map_nil, List.mem_singleton]
          rintro a ha b rfl rfl
          exact hfresh ha
        · rw [paperImpl_sign_signed request signed h, support_pure, Set.mem_singleton_iff] at hstep
          subst hstep
          exact ih _ signed hsigned inner hinner

/-- The lossy oracles behind the filter never see an epoch twice. -/
theorem lossyRun_filtered_valid {α : Type}
    (computation : OracleComp (spec + SigningSpec Msg Sig L) α) :
    ∀ z ∈ support ((simulateQ (lossyImpl cost scheme sk)
        ((simulateQ (filterImpl spec Msg Sig L) computation).run.run [])).run.run),
      SigningTranscript.Valid z.2 := by
  intro z hz
  have hmem := paperRun_nodup (cost := cost) (scheme := scheme) (sk := sk) computation [] (by simp)
  rw [paperRun_eq_filtered computation [], support_map] at hmem
  simpa [SigningTranscript.Valid] using hmem _ ⟨z, by simpa using hz, rfl⟩

end Runs

/-! ### The experiments -/

section Experiments

/-- The result of `jointRun`: the lossy run behind the filter, with its forgery, number of
repeated requests, requested epochs, counts and signing log, and the counts of key generation,
the verdict, and the counts of the verification. -/
abbrev JointResult (Msg Sig : Type) (L : ℕ) : Type :=
  ((((Forgery Msg Sig L × Multiplicative ℕ) × List (Fin L)) × Multiplicative QueryCounts) ×
    QueryLog (SigningSpec Msg Sig L)) × QueryCounts × Bool × QueryCounts

/-- The forgery of a joint result. -/
abbrev JointResult.forgery (result : JointResult Msg Sig L) : Forgery Msg Sig L := result.1.1.1.1.1

/-- The signing log of a joint result. -/
abbrev JointResult.log (result : JointResult Msg Sig L) : QueryLog (SigningSpec Msg Sig L) :=
  result.1.2

/-- The counts of the lossy experiment of the filtered adversary. -/
def JointResult.lossyCounts (result : JointResult Msg Sig L) : QueryCounts :=
  result.2.1 + Multiplicative.toAdd result.1.1.2 + result.2.2.2

/-- The counts of the statement's experiment, which also charges the repeated requests. -/
def JointResult.paperCounts (result : JointResult Msg Sig L) : QueryCounts :=
  result.2.1 + Multiplicative.toAdd (result.1.1.2 *
    Multiplicative.ofAdd (QueryCounts.single .sign (Multiplicative.toAdd result.1.1.1.1.2))) +
    result.2.2.2

theorem JointResult.lossyCounts_le (result : JointResult Msg Sig L) :
    result.lossyCounts ≤ result.paperCounts := by
  intro kind
  simp only [lossyCounts, paperCounts, toAdd_mul, toAdd_ofAdd, Pi.add_apply]
  omega

/-- Key generation, the filtered adversary with the lossy oracles, and the verification of its
forgery: the run behind both the statement's experiment of an adversary and the lossy experiment
of its filtered version. -/
def jointRun (cost : spec.Domain → ℕ) (scheme : EpochBasedSignature spec PK SK Msg Sig L)
    (adversary : Adversary spec PK Msg Sig L) : OracleComp spec (JointResult Msg Sig L) := do
  let ((pk, sk), keygenCounts) ←
    countQueries (fun t => QueryCounts.single .keygen (cost t)) scheme.keygen
  let z ← (simulateQ (lossyImpl cost scheme sk)
    ((simulateQ (filterImpl spec Msg Sig L) (adversary.main pk)).run.run [])).run.run
  let (verified, verifierCounts) ← countQueries (fun t => QueryCounts.single .verifier (cost t))
    (scheme.verify pk z.1.1.1.1.epoch z.1.1.1.1.message z.1.1.1.1.signature)
  return (z, keygenCounts, verified, verifierCounts)

theorem jointRun_valid (cost : spec.Domain → ℕ) (scheme : EpochBasedSignature spec PK SK Msg Sig L)
    (adversary : Adversary spec PK Msg Sig L) :
    ∀ result ∈ support (jointRun cost scheme adversary), SigningTranscript.Valid result.log := by
  intro result hresult
  simp only [jointRun, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hresult
  obtain ⟨keys, -, z, hz, verification, -, rfl⟩ := hresult
  exact lossyRun_filtered_valid _ z hz

variable [DecidableEq Msg] [DecidableEq Sig]

theorem experiment_eq_jointRun (cost : spec.Domain → ℕ)
    (scheme : EpochBasedSignature spec PK SK Msg Sig L) (adversary : Adversary spec PK Msg Sig L) :
    experiment cost scheme adversary =
      (fun result => (decide (¬SigningTranscript.Contains result.log result.forgery) &&
        result.2.2.1, result.paperCounts)) <$> jointRun cost scheme adversary := by
  unfold experiment jointRun
  simp only [paperRun_eq_filtered (cost := cost) (scheme := scheme), map_bind, bind_map_left,
    map_pure]
  rfl

theorem lossyExperiment_filtered_eq_jointRun (cost : spec.Domain → ℕ)
    (scheme : EpochBasedSignature spec PK SK Msg Sig L) (adversary : Adversary spec PK Msg Sig L) :
    lossyExperiment cost scheme (filtered adversary) =
      (fun result => (decide (SigningTranscript.Valid result.log ∧
        ¬SigningTranscript.Contains result.log result.forgery) && result.2.2.1,
        result.lossyCounts)) <$> jointRun cost scheme adversary := by
  unfold lossyExperiment jointRun filtered
  simp only [simulateQ_map, writerRun_map, logRun_map, map_bind, bind_map_left, map_pure,
    Functor.map_map]
  rfl

/-- An adversary with at most one signing request has the same experiment in both games. -/
theorem experiment_eq_lossy_of_oneRequest (cost : spec.Domain → ℕ)
    (scheme : EpochBasedSignature spec PK SK Msg Sig L) (adversary : Adversary spec PK Msg Sig L)
    (hone : OneRequest adversary) :
    experiment cost scheme adversary = lossyExperiment cost scheme adversary := by
  unfold experiment lossyExperiment
  refine bind_congr fun keys => ?_
  obtain ⟨⟨pk, sk⟩, keygenCounts⟩ := keys
  simp only
  rw [paperRun_eq_lossyRun_of_oneRequest _ (hone pk)]
  refine bind_congr_of_forall_mem_support _ fun z hz => ?_
  have hnodup := paperRun_nodup (cost := cost) (scheme := scheme) (sk := sk) (adversary.main pk) []
    (by simp) z (by rwa [paperRun_eq_lossyRun_of_oneRequest _ (hone pk)])
  have hvalid : SigningTranscript.Valid z.2 := hnodup
  obtain ⟨⟨forgery, counts⟩, log⟩ := z
  simp only at hvalid ⊢
  simp [hvalid]

end Experiments

section RandomOracle

variable {Input Output : Type} [DecidableEq Input] [SampleableType Output] [DecidableEq Msg]
  [DecidableEq Sig]

theorem randomOracle_run_map {α β : Type} (f : α → β)
    (computation : OracleComp (RandomOracleModel.World Input Output) α) :
    RandomOracleModel.run (f <$> computation) = f <$> RandomOracleModel.run computation := by
  simp [RandomOracleModel.run, simulateQ_map]

/-- Bit security in the lossy game gives bit security in the statement's game, in every
counting mode. -/
theorem hasClassicalSecurityBits_of_lossy
    (scheme : EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
    (Z : Finset QueryKind) (bits : ℕ)
    (h : (lossyGame (PK := PK) (SK := SK)).HasClassicalSecurityBits scheme Z bits) :
    (securityGame (PK := PK) (SK := SK)).HasClassicalSecurityBits scheme Z bits := by
  intro q hq adversary hbound
  let joint := RandomOracleModel.run
    (jointRun (RandomOracleModel.hashCost Input Output) scheme adversary)
  have hvalid : ∀ result ∈ support joint, SigningTranscript.Valid result.log := fun result hr =>
    jointRun_valid _ scheme adversary result (support_simulateQ_run'_subset _ _ _ hr)
  have hpaper : (securityGame (PK := PK) (SK := SK)).experiment scheme adversary =
      (fun result => (decide (¬SigningTranscript.Contains result.log result.forgery) &&
        result.2.2.1, result.paperCounts)) <$> joint := by
    show RandomOracleModel.run (experiment _ scheme adversary) = _
    rw [experiment_eq_jointRun, randomOracle_run_map]
  have hlossy : (lossyGame (PK := PK) (SK := SK)).experiment scheme (filtered adversary) =
      (fun result => (decide (SigningTranscript.Valid result.log ∧
        ¬SigningTranscript.Contains result.log result.forgery) && result.2.2.1,
        result.lossyCounts)) <$> joint := by
    show RandomOracleModel.run (lossyExperiment _ scheme (filtered adversary)) = _
    rw [lossyExperiment_filtered_eq_jointRun, randomOracle_run_map]
  have hadv : (securityGame (PK := PK) (SK := SK)).advantage scheme adversary =
      (lossyGame (PK := PK) (SK := SK)).advantage scheme (filtered adversary) := by
    simp only [SecurityGame.advantage, hpaper, hlossy, probEvent_map]
    refine probEvent_ext fun result hr => ?_
    simp [Function.comp, hvalid result hr]
  have hboundLossy : (lossyGame (PK := PK) (SK := SK)).HasQueryBound scheme Z
      (filtered adversary) q := by
    unfold SecurityGame.HasQueryBound at hbound ⊢
    rw [hpaper, probEvent_map] at hbound
    rw [hlossy, probEvent_map]
    refine le_antisymm probEvent_le_one (hbound ▸ probEvent_mono fun result _ hr => ?_)
    exact le_trans (Finset.sum_le_sum fun kind _ => result.lossyCounts_le kind) hr
  rw [hadv]
  exact h q hq _ hboundLossy

/-- An adversary with at most one signing request has the same experiment in the statement's
game as in the lossy game. -/
theorem securityGame_experiment_eq_lossy_of_oneRequest
    (scheme : EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
    (adversary : Adversary (RandomOracleModel.World Input Output) PK Msg Sig L)
    (hone : OneRequest adversary) :
    (securityGame (PK := PK) (SK := SK)).experiment scheme adversary =
      (lossyGame (PK := PK) (SK := SK)).experiment scheme adversary := by
  show RandomOracleModel.run (experiment _ scheme adversary) =
    RandomOracleModel.run (lossyExperiment _ scheme adversary)
  rw [experiment_eq_lossy_of_oneRequest _ scheme adversary hone]

end RandomOracle


end XmssSecurity.SUFCMA

namespace XmssSecurity.EUFCMA

open SUFCMA

variable {ι : Type} {spec : OracleSpec ι} {PK SK Msg Sig : Type} {L : ℕ}

section Experiments

variable [DecidableEq Msg]

theorem experiment_eq_jointRun (cost : spec.Domain → ℕ)
    (scheme : EpochBasedSignature spec PK SK Msg Sig L) (adversary : Adversary spec PK Msg Sig L) :
    EUFCMA.experiment cost scheme adversary =
      (fun result => (decide (¬SigningTranscript.ContainsRequest result.log result.forgery) &&
        result.2.2.1, result.paperCounts)) <$> jointRun cost scheme adversary := by
  unfold EUFCMA.experiment jointRun
  simp only [paperRun_eq_filtered (cost := cost) (scheme := scheme), map_bind, bind_map_left,
    map_pure]
  rfl

theorem lossyExperiment_filtered_eq_jointRun (cost : spec.Domain → ℕ)
    (scheme : EpochBasedSignature spec PK SK Msg Sig L) (adversary : Adversary spec PK Msg Sig L) :
    EUFCMA.lossyExperiment cost scheme (filtered adversary) =
      (fun result => (decide (SigningTranscript.Valid result.log ∧
        ¬SigningTranscript.ContainsRequest result.log result.forgery) && result.2.2.1,
        result.lossyCounts)) <$> jointRun cost scheme adversary := by
  unfold EUFCMA.lossyExperiment jointRun filtered
  simp only [simulateQ_map, writerRun_map, logRun_map, map_bind, bind_map_left, map_pure,
    Functor.map_map]
  rfl

/-- An adversary with at most one signing request has the same experiment in both games. -/
theorem experiment_eq_lossy_of_oneRequest (cost : spec.Domain → ℕ)
    (scheme : EpochBasedSignature spec PK SK Msg Sig L) (adversary : Adversary spec PK Msg Sig L)
    (hone : OneRequest adversary) :
    EUFCMA.experiment cost scheme adversary = EUFCMA.lossyExperiment cost scheme adversary := by
  unfold EUFCMA.experiment EUFCMA.lossyExperiment
  refine bind_congr fun keys => ?_
  obtain ⟨⟨pk, sk⟩, keygenCounts⟩ := keys
  simp only
  rw [paperRun_eq_lossyRun_of_oneRequest _ (hone pk)]
  refine bind_congr_of_forall_mem_support _ fun z hz => ?_
  have hnodup := paperRun_nodup (cost := cost) (scheme := scheme) (sk := sk) (adversary.main pk) []
    (by simp) z (by rwa [paperRun_eq_lossyRun_of_oneRequest _ (hone pk)])
  have hvalid : SigningTranscript.Valid z.2 := hnodup
  obtain ⟨⟨forgery, counts⟩, log⟩ := z
  simp only at hvalid ⊢
  simp [hvalid]

end Experiments

section RandomOracle

variable {Input Output : Type} [DecidableEq Input] [SampleableType Output] [DecidableEq Msg]

/-- Bit security in the lossy game gives bit security in the statement's game, in every
counting mode. -/
theorem hasClassicalSecurityBits_of_lossy
    (scheme : EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
    (Z : Finset QueryKind) (bits : ℕ)
    (h : (EUFCMA.lossyGame (PK := PK) (SK := SK)).HasClassicalSecurityBits scheme Z bits) :
    (EUFCMA.securityGame (PK := PK) (SK := SK)).HasClassicalSecurityBits scheme Z bits := by
  intro q hq adversary hbound
  let joint := RandomOracleModel.run
    (jointRun (RandomOracleModel.hashCost Input Output) scheme adversary)
  have hvalid : ∀ result ∈ support joint, SigningTranscript.Valid result.log := fun result hr =>
    jointRun_valid _ scheme adversary result (support_simulateQ_run'_subset _ _ _ hr)
  have hpaper : (EUFCMA.securityGame (PK := PK) (SK := SK)).experiment scheme adversary =
      (fun result => (decide (¬SigningTranscript.ContainsRequest result.log result.forgery) &&
        result.2.2.1, result.paperCounts)) <$> joint := by
    show RandomOracleModel.run (EUFCMA.experiment _ scheme adversary) = _
    rw [experiment_eq_jointRun, SUFCMA.randomOracle_run_map]
  have hlossy : (EUFCMA.lossyGame (PK := PK) (SK := SK)).experiment scheme (filtered adversary) =
      (fun result => (decide (SigningTranscript.Valid result.log ∧
        ¬SigningTranscript.ContainsRequest result.log result.forgery) && result.2.2.1,
        result.lossyCounts)) <$> joint := by
    show RandomOracleModel.run (EUFCMA.lossyExperiment _ scheme (filtered adversary)) = _
    rw [lossyExperiment_filtered_eq_jointRun, SUFCMA.randomOracle_run_map]
  have hadv : (EUFCMA.securityGame (PK := PK) (SK := SK)).advantage scheme adversary =
      (EUFCMA.lossyGame (PK := PK) (SK := SK)).advantage scheme (filtered adversary) := by
    simp only [SecurityGame.advantage, hpaper, hlossy, probEvent_map]
    refine probEvent_ext fun result hr => ?_
    simp [Function.comp, hvalid result hr]
  have hboundLossy : (EUFCMA.lossyGame (PK := PK) (SK := SK)).HasQueryBound scheme Z
      (filtered adversary) q := by
    unfold SecurityGame.HasQueryBound at hbound ⊢
    rw [hpaper, probEvent_map] at hbound
    rw [hlossy, probEvent_map]
    refine le_antisymm probEvent_le_one (hbound ▸ probEvent_mono fun result _ hr => ?_)
    exact le_trans (Finset.sum_le_sum fun kind _ => result.lossyCounts_le kind) hr
  rw [hadv]
  exact h q hq _ hboundLossy

/-- An adversary with at most one signing request has the same experiment in the statement's
game as in the lossy game. -/
theorem securityGame_experiment_eq_lossy_of_oneRequest
    (scheme : EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
    (adversary : Adversary (RandomOracleModel.World Input Output) PK Msg Sig L)
    (hone : OneRequest adversary) :
    (EUFCMA.securityGame (PK := PK) (SK := SK)).experiment scheme adversary =
      (EUFCMA.lossyGame (PK := PK) (SK := SK)).experiment scheme adversary := by
  show RandomOracleModel.run (EUFCMA.experiment _ scheme adversary) =
    RandomOracleModel.run (EUFCMA.lossyExperiment _ scheme adversary)
  rw [experiment_eq_lossy_of_oneRequest _ scheme adversary hone]

end RandomOracle

end XmssSecurity.EUFCMA

namespace XmssSecurity.Modes

open SUFCMA

variable {PK SK Msg Sig : Type} {L : ℕ} {Input Output : Type} [DecidableEq Input]
  [SampleableType Output] [DecidableEq Msg]

/-- Bit security in the statement's SUF-CMA game bounds every adversary of the per-mode notion
that makes at most one signing request. The attacks of the proofs are such adversaries. -/
theorem notion_oneRequest_bound [DecidableEq Sig] (Z : Finset QueryKind)
    (hZ : QueryKind.hash ∈ Z)
    (scheme : EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
    (bits : ℕ)
    (h : (SUFCMA.securityGame (PK := PK) (SK := SK)).HasClassicalSecurityBits scheme Z bits) :
    ∀ q, 1 ≤ q → ∀ adversary, OneRequest adversary →
      (notion (modeOf Z)).HasQueryBound scheme adversary q →
      (notion (modeOf Z)).advantage scheme adversary ≤ q / ((2 ^ bits : ℕ) : ℝ≥0∞) := by
  intro q hq adversary hone hbound
  have hexp := securityGame_experiment_eq_lossy_of_oneRequest scheme adversary hone
  have hadv : (SUFCMA.securityGame (PK := PK) (SK := SK)).advantage scheme adversary =
      (notion (modeOf Z)).advantage scheme adversary := by
    simp only [SecurityGame.advantage, SecurityNotion.advantage, hexp]
    simp only [SUFCMA.lossyGame, notion_experiment_eq Z hZ scheme adversary, probEvent_map]
    rfl
  have hbound' : (SUFCMA.securityGame (PK := PK) (SK := SK)).HasQueryBound scheme Z adversary q := by
    simp only [SecurityGame.HasQueryBound, hexp]
    simpa only [SecurityNotion.HasQueryBound, notion_experiment_eq Z hZ scheme adversary,
      probEvent_eq_one_iff, probFailure_eq_zero, true_and, support_map, Set.mem_image,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] using hbound
  rw [← hadv]
  exact h q hq adversary hbound'

/-- The EUF-CMA counterpart of `notion_oneRequest_bound`. -/
theorem eufNotion_oneRequest_bound (Z : Finset QueryKind) (hZ : QueryKind.hash ∈ Z)
    (scheme : EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
    (bits : ℕ)
    (h : (EUFCMA.securityGame (PK := PK) (SK := SK)).HasClassicalSecurityBits scheme Z bits) :
    ∀ q, 1 ≤ q → ∀ adversary, OneRequest adversary →
      (EUFCMA.notion (modeOf Z)).HasQueryBound scheme adversary q →
      (EUFCMA.notion (modeOf Z)).advantage scheme adversary ≤ q / ((2 ^ bits : ℕ) : ℝ≥0∞) := by
  intro q hq adversary hone hbound
  have hexp := EUFCMA.securityGame_experiment_eq_lossy_of_oneRequest scheme adversary hone
  have hadv : (EUFCMA.securityGame (PK := PK) (SK := SK)).advantage scheme adversary =
      (EUFCMA.notion (modeOf Z)).advantage scheme adversary := by
    simp only [SecurityGame.advantage, SecurityNotion.advantage, hexp]
    simp only [EUFCMA.lossyGame, eufNotion_experiment_eq Z hZ scheme adversary, probEvent_map]
    rfl
  have hbound' : (EUFCMA.securityGame (PK := PK) (SK := SK)).HasQueryBound scheme Z adversary q := by
    simp only [SecurityGame.HasQueryBound, hexp]
    simpa only [SecurityNotion.HasQueryBound, eufNotion_experiment_eq Z hZ scheme adversary,
      probEvent_eq_one_iff, probFailure_eq_zero, true_and, support_map, Set.mem_image,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] using hbound
  rw [← hadv]
  exact h q hq adversary hbound'

/-- Bit security in the statement's game is monotone in the counting mode: charging more kinds
of queries only helps. -/
theorem securityGame_hasClassicalSecurityBits_mono {Scheme Kind : Type}
    (game : SecurityGame Scheme Kind) (scheme : Scheme) {Z Z' : Finset Kind} (hsub : Z ⊆ Z')
    {bits : ℕ} (h : game.HasClassicalSecurityBits scheme Z bits) :
    game.HasClassicalSecurityBits scheme Z' bits := by
  intro q hq adversary hbound
  refine h q hq adversary ?_
  unfold SecurityGame.HasQueryBound at hbound ⊢
  refine le_antisymm probEvent_le_one (hbound ▸ probEvent_mono fun result _ hr => ?_)
  exact le_trans (Finset.sum_le_sum_of_subset hsub) hr

end XmssSecurity.Modes
