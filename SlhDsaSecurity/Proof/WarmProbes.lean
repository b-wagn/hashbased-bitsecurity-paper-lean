import SlhDsaSecurity.Proof.LazyBudget

/-!
# How many of a lazy run's probes the budget pays for

`SensitiveQuery.prob_record_sensitive_le` charges one unit of `2 ^ -128` per entry of the record
it is handed, so the half costs whatever that record's length is bounded by. The record the
charge consumes is `OpenCache.lazyProgram`'s own: each probe paired with the cache it was issued
against. The question this file settles is how long that list can be.

**The whole list is not bounded by the budget, and the gap is not small.** The stripped honest
phase still asks about the inputs the walk's table cannot answer — the message digest and its
randomiser, which depend on the adversary's message and so are in no fixed table — and those
calls are charged to `Counts.signing`, which `Counts.work` does not read. A run may make
`2 ^ 64` signing requests inside the budget, so the raw probe count can exceed the work by
`2 ^ 64`, and a charge of `2 ^ 64 / 2 ^ 128` would sink the half on its own.

**The entries that cost nothing are exactly the ones that are not bounded.** A probe is
sensitive only if it is the canonical input of a node, and the walk's table holds an entry at
every canonical input, so a sensitive probe is one the table answers. The honest phase's
remaining probes are the ones the table *cannot* answer — that is the defining property of
stripping. So handing the charge only the probes the table answers drops no sensitive entry and
drops every honest one.

`warmCount` is that filtered length, and `warmCount_strippedAfterSeeds` bounds it by the work
the outcome reports: key generation and the signer contribute nothing because stripping leaves
them asking only cold inputs, while the adversary's own queries and the verifier's are charged
one for one. With `LazyBudget.work_add_pow_le_of_budget_lazy` that is a bound by the budget less
what key generation spent, which is the room the forgery's own claimed cells are paid out of.

`exists_mem_warmProbes` is the other half of the trade, and it is where the filter has to be
justified at the point of use: whatever property the charge is about, it must be one only an
input the table answers can have.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.WarmProbes

open Security OpenCache CanonicalGraph LazyBudget

/-- The probes a run has recorded at inputs the walk's table answers. -/
def warmCount (warm : QueryCache HashSpec)
    (probes : List (Bytes × QueryCache HashSpec)) : Nat :=
  probes.countP (fun entry => (warm entry.1).isSome)

theorem warmCount_append (warm : QueryCache HashSpec)
    (left right : List (Bytes × QueryCache HashSpec)) :
    warmCount warm (left ++ right) = warmCount warm left + warmCount warm right :=
  List.countP_append

theorem warmCount_singleton_le (warm : QueryCache HashSpec)
    (entry : Bytes × QueryCache HashSpec) : warmCount warm [entry] ≤ 1 := by
  rw [warmCount, List.countP_singleton]
  split <;> simp

theorem warmCount_singleton_cold (warm : QueryCache HashSpec)
    (entry : Bytes × QueryCache HashSpec) (hcold : warm entry.1 = none) :
    warmCount warm [entry] = 0 := by
  rw [warmCount, List.countP_singleton, if_neg (by simp [hcold])]

/-! ## One step

A hash call appends one probe and a private sample appends none, so a step records at most what
the hash counter charges it — and nothing at all when the table cannot answer the input, which
is the case the honest phase is in. -/

/-- The probes a hash call appends. -/
theorem lazyProgram_hash_probes (publicSeed : Digest)
    (availableAt : QueryCache HashSpec → Node → Prop) (table : Cells × Padding)
    (input : Bytes) (state : HandlerState) (z : HashOutput × HandlerState)
    (hz : z ∈ support
      (((lazyProgram publicSeed availableAt table) (Sum.inr input)).run state)) :
    z.2.2.1 = state.2.1 ++ [(input, state.1)] := by
  have hbind : z ∈ support
      (lazyAnswer publicSeed availableAt table input state.1 >>= fun step =>
        (pure (step.1, (step.2, state.2.1 ++ [(input, state.1)], state.2.2 + 1)) :
          ProbComp (HashOutput × HandlerState))) := hz
  rw [mem_support_bind_iff] at hbind
  obtain ⟨step, -, hpure⟩ := hbind
  rw [support_pure, Set.mem_singleton_iff] at hpure
  rw [hpure]

/-- **A hash call the table cannot answer records nothing that matters.** -/
theorem warmCount_hash_cold (publicSeed : Digest)
    (availableAt : QueryCache HashSpec → Node → Prop) (table : Cells × Padding)
    (warm : QueryCache HashSpec) (input : Bytes) (hcold : warm input = none)
    (state : HandlerState) (z : HashOutput × HandlerState)
    (hz : z ∈ support
      (((lazyProgram publicSeed availableAt table) (Sum.inr input)).run state)) :
    warmCount warm z.2.2.1 = warmCount warm state.2.1 := by
  rw [lazyProgram_hash_probes publicSeed availableAt table input state z hz, warmCount_append,
    warmCount_singleton_cold warm _ hcold, Nat.add_zero]

/-- **A hash call records at most one probe that matters.** -/
theorem warmCount_hash_le (publicSeed : Digest)
    (availableAt : QueryCache HashSpec → Node → Prop) (table : Cells × Padding)
    (warm : QueryCache HashSpec) (input : Bytes) (state : HandlerState)
    (z : HashOutput × HandlerState)
    (hz : z ∈ support
      (((lazyProgram publicSeed availableAt table) (Sum.inr input)).run state)) :
    warmCount warm z.2.2.1 ≤ warmCount warm state.2.1 + 1 := by
  rw [lazyProgram_hash_probes publicSeed availableAt table input state z hz, warmCount_append]
  exact Nat.add_le_add_left (warmCount_singleton_le warm _) _

/-- **A step records at most what the hash counter charges it.** -/
theorem warmCount_step_le (publicSeed : Digest)
    (availableAt : QueryCache HashSpec → Node → Prop) (table : Cells × Padding)
    (warm : QueryCache HashSpec) (queried : OracleWorld.Domain) (state : HandlerState)
    (z : OracleWorld.Range queried × HandlerState)
    (hz : z ∈ support (((lazyProgram publicSeed availableAt table) queried).run state)) :
    warmCount warm z.2.2.1 ≤ warmCount warm state.2.1 + hashCost queried := by
  rcases queried with coin | input
  · rw [lazyProgram_run_inl, mem_support_bind_iff] at hz
    obtain ⟨value, -, hpure⟩ := hz
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [show z.2 = state from by rw [hpure]]
    exact Nat.le_add_right _ _
  · exact warmCount_hash_le publicSeed availableAt table warm input state z hz

/-! ## The honest phase records nothing that matters

Stripping answers the honest parties from the walk's table wherever it can, so the only inputs
they ask about are the ones the table cannot answer — and those are exactly the probes the
count ignores. -/

/-- A query the table cannot answer, followed by a run that records nothing that matters. -/
theorem warmCount_cold_query_bind {α : Type} (publicSeed : Digest)
    (availableAt : QueryCache HashSpec → Node → Prop) (table : Cells × Padding)
    (warm : QueryCache HashSpec) (input : Bytes) (hcold : warm input = none)
    (next : HashOutput → OracleComp OracleWorld α)
    (hnext : ∀ (value : HashOutput) (inner : HandlerState) (y : α × HandlerState),
      y ∈ support
        ((simulateQ (lazyProgram publicSeed availableAt table) (next value)).run inner) →
        warmCount warm y.2.2.1 = warmCount warm inner.2.1)
    (state : HandlerState) (z : α × HandlerState)
    (hz : z ∈ support ((simulateQ (lazyProgram publicSeed availableAt table)
      (liftM (OracleWorld.query (Sum.inr input)) >>= next)).run state)) :
    warmCount warm z.2.2.1 = warmCount warm state.2.1 := by
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨step, hstep, hrest⟩ := hz
  rw [hnext step.1 step.2 z hrest]
  exact warmCount_hash_cold publicSeed availableAt table warm input hcold state step hstep

/-- **A stripped hash-only computation records nothing that matters.** -/
theorem warmCount_strip {α : Type} (publicSeed : Digest)
    (availableAt : QueryCache HashSpec → Node → Prop) (table : Cells × Padding)
    (warm : QueryCache HashSpec) (computation : OracleComp HashSpec α) :
    ∀ (state : HandlerState) (z : α × HandlerState),
      z ∈ support ((simulateQ (lazyProgram publicSeed availableAt table)
        (OracleComp.liftComp (simulateQ (StripCached.stripImpl warm) computation)
          OracleWorld)).run state) →
        warmCount warm z.2.2.1 = warmCount warm state.2.1 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state z hz
    rw [simulateQ_pure, OracleComp.liftComp_pure, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    rw [show z.2 = state from by rw [hz]]
  | query_bind input next ih =>
    intro state z hz
    rw [simulateQ_bind, show simulateQ (StripCached.stripImpl warm)
        (liftM (OracleSpec.query input) : OracleComp HashSpec HashOutput) =
        StripCached.stripImpl warm input from by simp,
      OracleComp.liftComp_bind] at hz
    cases hwarm : warm input with
    | some value =>
      rw [show StripCached.stripImpl warm input =
          (pure value : OracleComp HashSpec HashOutput) from by
        simp [StripCached.stripImpl, hwarm], OracleComp.liftComp_pure, pure_bind] at hz
      exact ih value state z hz
    | none =>
      rw [show StripCached.stripImpl warm input =
          (liftM (OracleSpec.query input) : OracleComp HashSpec HashOutput) from by
        simp [StripCached.stripImpl, hwarm]] at hz
      exact warmCount_cold_query_bind publicSeed availableAt table warm input hwarm
        (fun value => OracleComp.liftComp
          (simulateQ (StripCached.stripImpl warm) (next value)) OracleWorld) ih state z hz

attribute [local irreducible] Scheme.keygenInternal Scheme.sign Scheme.verify

/-- Stripped key generation records nothing that matters. -/
theorem warmCount_strippedKeygen (publicSeed : Digest)
    (availableAt : QueryCache HashSpec → Node → Prop) (table : Cells × Padding)
    (warm : QueryCache HashSpec) (sds : Digest × Digest × Digest) (state : HandlerState)
    (z : (SecretKey × PublicKey) × HandlerState)
    (hz : z ∈ support ((simulateQ (lazyProgram publicSeed availableAt table)
      (StrippedGame.strippedKeygen warm sds)).run state)) :
    warmCount warm z.2.2.1 = warmCount warm state.2.1 :=
  warmCount_strip publicSeed availableAt table warm
    (Scheme.keygenInternal (m := OracleComp HashSpec) sds.1 sds.2.1 sds.2.2) state z hz

/-- The stripped signer records nothing that matters. -/
theorem warmCount_strippedSign (publicSeed : Digest)
    (availableAt : QueryCache HashSpec → Node → Prop) (table : Cells × Padding)
    (warm : QueryCache HashSpec) (sk : SecretKey) (request : Message) (state : HandlerState)
    (z : Option Bytes × HandlerState)
    (hz : z ∈ support ((simulateQ (lazyProgram publicSeed availableAt table)
      (StrippedGame.strippedSign warm sk request)).run state)) :
    warmCount warm z.2.2.1 = warmCount warm state.2.1 :=
  warmCount_strip publicSeed availableAt table warm
    (Scheme.sign (m := OracleComp HashSpec) sk request) state z hz

/-! ## The adversary's own phase

The adversary's own oracle forwards one query and charges one hash call; the signing oracle
charges a request, which the work budget does not read, and runs the stripped signer, which
records nothing that matters. So the phase records at most the work it charges. -/

/-- One of the adversary's own queries records at most what it charges. -/
theorem warmCount_adversaryImpl (publicSeed : Digest)
    (availableAt : QueryCache HashSpec → Node → Prop) (table : Cells × Padding)
    (warm : QueryCache HashSpec) (queried : OracleWorld.Domain) (log : SigningLog)
    (state : HandlerState)
    (outer : ((OracleWorld.Range queried × Multiplicative Counts) × SigningLog) × HandlerState)
    (houter : outer ∈ support ((simulateQ (lazyProgram publicSeed availableAt table)
      ((WriterT.run (AdversaryQueries.adversaryImpl queried)).run log)).run state)) :
    warmCount warm outer.2.2.1 ≤
      warmCount warm state.2.1 + (Multiplicative.toAdd outer.1.1.2).work := by
  rw [AdversaryQueries.run_adversaryImpl, simulateQ_map, StateT.run_map, support_map] at houter
  obtain ⟨inner, hinner, heq⟩ := houter
  rw [simulateQ_spec_query] at hinner
  rw [show outer.1.1.2 =
      Multiplicative.ofAdd (Counts.single .hash (hashCost queried)) from by rw [← heq],
    show outer.2 = inner.2 from by rw [← heq]]
  rw [toAdd_ofAdd, AdversaryQueries.work_single_hash]
  exact warmCount_step_le publicSeed availableAt table warm queried state inner hinner

/-- A signing request records nothing that matters, and charges nothing to the work budget. -/
theorem warmCount_strippedSigningOracle (publicSeed : Digest)
    (availableAt : QueryCache HashSpec → Node → Prop) (table : Cells × Padding)
    (warm : QueryCache HashSpec) (sk : SecretKey) (request : Message) (log : SigningLog)
    (state : HandlerState)
    (outer : ((Option Bytes × Multiplicative Counts) × SigningLog) × HandlerState)
    (houter : outer ∈ support ((simulateQ (lazyProgram publicSeed availableAt table)
      ((WriterT.run (StrippedGame.strippedSigningOracle warm sk request)).run log)).run state)) :
    warmCount warm outer.2.2.1 ≤
      warmCount warm state.2.1 + (Multiplicative.toAdd outer.1.1.2).work := by
  rw [StrippedGame.strippedSigningOracle, StrippedGame.run_signingOracleWith, simulateQ_bind,
    StateT.run_bind, mem_support_bind_iff] at houter
  obtain ⟨step, hstep, hrest⟩ := houter
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hrest
  rw [show outer.2 = step.2 from by rw [hrest],
    warmCount_strippedSign publicSeed availableAt table warm sk request state step hstep]
  exact Nat.le_add_right _ _

set_option maxHeartbeats 1000000 in
/-- **The adversary's phase records at most the work it charges.** -/
theorem warmCount_adversary (publicSeed : Digest)
    (availableAt : QueryCache HashSpec → Node → Prop) (table : Cells × Padding)
    (warm : QueryCache HashSpec) (sk : SecretKey) {α : Type}
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (log : SigningLog) (state : HandlerState)
      (result : ((α × Multiplicative Counts) × SigningLog) × HandlerState),
      result ∈ support ((simulateQ (lazyProgram publicSeed availableAt table)
        ((WriterT.run (simulateQ (AdversaryQueries.adversaryImpl +
          StrippedGame.strippedSigningOracle warm sk) computation)).run log)).run state) →
        warmCount warm result.2.2.1 ≤
          warmCount warm state.2.1 + (Multiplicative.toAdd result.1.1.2).work := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro log state result hmem
    rw [simulateQ_pure, show ((WriterT.run (pure value : CountedRun α)).run log) =
        (pure ((value, (1 : Multiplicative Counts)), log) :
          OracleComp OracleWorld ((α × Multiplicative Counts) × SigningLog)) from rfl,
      simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [show result.2 = state from by rw [hmem]]
    exact Nat.le_add_right _ _
  | query_bind queried next ih =>
    intro log state result hmem
    rw [simulateQ_bind, simulateQ_spec_query, AdversaryQueries.run_counted_bind, simulateQ_bind,
      StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨outer, houter, hrest⟩ := hmem
    rw [simulateQ_map, StateT.run_map, support_map] at hrest
    obtain ⟨inner, hinner, heq⟩ := hrest
    have htail := ih outer.1.1.1 outer.1.2 outer.2 inner hinner
    have hhead : warmCount warm outer.2.2.1 ≤
        warmCount warm state.2.1 + (Multiplicative.toAdd outer.1.1.2).work := by
      rcases queried with world | request
      · exact warmCount_adversaryImpl publicSeed availableAt table warm world log state outer
          houter
      · exact warmCount_strippedSigningOracle publicSeed availableAt table warm sk request log
          state outer houter
    have hvalue : result.1.1.2 = outer.1.1.2 * inner.1.1.2 := by
      rw [← congrArg (fun z => z.1.1.2) heq]
    have hstate : result.2 = inner.2 := by rw [← congrArg Prod.snd heq]
    rw [hstate, hvalue, toAdd_mul, AdversaryQueries.work_add, ← Nat.add_assoc]
    exact le_trans htail (Nat.add_le_add_right hhead _)

/-! ## The verifier's phase

The verifier is instrumented rather than handled, so its charge is a counter inside the
computation; every hash call it makes is charged, so the phase records at most the work it
charges. -/

set_option maxHeartbeats 1000000 in
/-- **An instrumentation that charges one kind per hash call bounds what the run records.** -/
theorem warmCount_countQueries (publicSeed : Digest)
    (availableAt : QueryCache HashSpec → Node → Prop) (table : Cells × Padding)
    (warm : QueryCache HashSpec) (kind : QueryKind) (hkind : kind ≠ .signing) {α : Type}
    (computation : OracleComp OracleWorld α) :
    ∀ (state : HandlerState) (result : (α × Counts) × HandlerState),
      result ∈ support ((simulateQ (lazyProgram publicSeed availableAt table)
        (countQueries (fun input => Counts.single kind (hashCost input))
          computation)).run state) →
        warmCount warm result.2.2.1 ≤ warmCount warm state.2.1 + (result.1.2).work := by
  have hwork : ∀ count : Nat, (Counts.single kind count).work = count := by
    intro count
    rcases kind with _ | _ | _
    · exact absurd rfl hkind
    · exact AdversaryQueries.work_single_hash count
    · exact AdversaryQueries.work_single_verification count
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state result hmem
    rw [VerificationBudget.countQueries_pure, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hmem
    rw [show result.2 = state from by rw [hmem]]
    exact Nat.le_add_right _ _
  | query_bind queried next ih =>
    intro state result hmem
    rw [WarmedSplit.countQueries_query_bind, simulateQ_bind, simulateQ_spec_query,
      StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    rw [simulateQ_map, StateT.run_map, support_map] at hrest
    obtain ⟨inner, hinner, heq⟩ := hrest
    have htail := ih step.1 step.2 inner hinner
    have hhead := warmCount_step_le publicSeed availableAt table warm queried state step hstep
    have hvalue : result.1.2 = Counts.single kind (hashCost queried) + inner.1.2 := by
      rw [← congrArg (fun z => z.1.2) heq]
    have hstate : result.2 = inner.2 := by rw [← congrArg Prod.snd heq]
    rw [hstate, hvalue, AdversaryQueries.work_add, hwork]
    omega

/-! ## The whole stripped game -/

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 1000000 in
/-- **A run of the stripped game records at most the work the outcome reports.** The honest
phase records nothing the count sees, and the adversary's and the verifier's own calls are
exactly what the outcome charges. -/
theorem warmCount_strippedAfterSeeds (publicSeed : Digest)
    (availableAt : QueryCache HashSpec → Node → Prop) (table : Cells × Padding)
    (adversary : Adversary) (sds : Digest × Digest × Digest) (warm : QueryCache HashSpec)
    (state : HandlerState) (result : Outcome × HandlerState)
    (hmem : result ∈ support ((simulateQ (lazyProgram publicSeed availableAt table)
      (StrippedGame.strippedAfterSeeds adversary sds warm)).run state)) :
    warmCount warm result.2.2.1 ≤ warmCount warm state.2.1 + result.1.counts.work := by
  unfold StrippedGame.strippedAfterSeeds at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨sk, pk⟩, keyState⟩, hkeys, hmem⟩ := hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨⟨forgery, advCounts⟩, signed⟩, advState⟩, hadv, hmem⟩ := hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨verified, verifierCounts⟩, verifyState⟩, hverify, hmem⟩ := hmem
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
  have hkeygen := warmCount_strippedKeygen publicSeed availableAt table warm sds state
    ⟨⟨sk, pk⟩, keyState⟩ hkeys
  have hphase := warmCount_adversary publicSeed availableAt table warm sk (adversary.main pk)
    [] keyState ⟨⟨⟨forgery, advCounts⟩, signed⟩, advState⟩ hadv
  have hverifier := warmCount_countQueries publicSeed availableAt table warm .verification
    (by decide) (Scheme.verify pk forgery.message forgery.signature) advState
    ⟨⟨verified, verifierCounts⟩, verifyState⟩ hverify
  rw [show result.2 = verifyState from by rw [hmem],
    show result.1.counts = Multiplicative.toAdd advCounts + verifierCounts from by rw [hmem],
    AdversaryQueries.work_add]
  simp only at hkeygen hphase hverifier
  omega

/-! ## The list the charge is handed

The charge takes the probes as a list and pays one unit per entry, so what is handed to it is
the probes the table answers rather than all of them. That loses nothing: a sensitive candidate
is the canonical input of a node, and the walk's table has an entry at every canonical input, so
no sensitive entry is dropped. What it gains is the bound, since the entries it drops are the
honest phase's, which the work budget does not pay for. -/

/-- The probes at inputs the walk's table answers. -/
def warmProbes (warm : QueryCache HashSpec)
    (probes : List (Bytes × QueryCache HashSpec)) : List (Bytes × QueryCache HashSpec) :=
  probes.filter (fun entry => (warm entry.1).isSome)

theorem length_warmProbes (warm : QueryCache HashSpec)
    (probes : List (Bytes × QueryCache HashSpec)) :
    (warmProbes warm probes).length = warmCount warm probes :=
  List.countP_eq_length_filter.symm

/-- **No entry the table answers is dropped.** -/
theorem mem_warmProbes (warm : QueryCache HashSpec)
    (probes : List (Bytes × QueryCache HashSpec)) (entry : Bytes × QueryCache HashSpec)
    (hmem : entry ∈ probes) (hwarm : warm entry.1 ≠ none) : entry ∈ warmProbes warm probes :=
  List.mem_filter.mpr ⟨hmem, Option.isSome_iff_ne_none.mpr hwarm⟩

/-- **An event about the probes the table answers is the event about all of them**, for any
property only an input the table answers can have. -/
theorem exists_mem_warmProbes (warm : QueryCache HashSpec)
    (probes : List (Bytes × QueryCache HashSpec))
    (Holds : Bytes × QueryCache HashSpec → Prop)
    (hwarm : ∀ entry, Holds entry → warm entry.1 ≠ none)
    (hexists : ∃ entry ∈ probes, Holds entry) :
    ∃ entry ∈ warmProbes warm probes, Holds entry := by
  obtain ⟨entry, hmem, hholds⟩ := hexists
  exact ⟨entry, mem_warmProbes warm probes entry hmem (hwarm entry hholds), hholds⟩

/-! ## The deliverable -/

open Security WarmedGame

/-- **The probes the charge is handed fit the budget, with key generation's spend reserved.** -/
theorem warmCount_add_pow_le_of_budget {adversary : Adversary} {q : Nat}
    (hbudget : HasTotalBudget adversary q)
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk) (publicSeed : Digest)
    (availableAt : QueryCache HashSpec → Node → Prop) (table : Cells × Padding)
    (state : HandlerState) (hstate : state.1 = walk.2) (hstart : state.2.1 = [])
    {result : Outcome × HandlerState}
    (hresult : result ∈ support
      ((simulateQ (lazyProgram publicSeed availableAt table)
        (StrippedGame.strippedAfterSeeds adversary walk.1.1 walk.2)).run state)) :
    warmCount walk.2 result.2.2.1 + 2 ^ subtreeHeight ≤ q := by
  have hrecord := warmCount_strippedAfterSeeds publicSeed availableAt table adversary walk.1.1
    walk.2 state result hresult
  rw [hstart] at hrecord
  have hbound := LazyBudget.work_add_pow_le_of_budget_lazy hbudget hwalk publicSeed availableAt
    table state hstate hresult
  rw [show warmCount walk.2 [] = 0 from rfl] at hrecord
  omega

/-- The same, as the length of the list the charge is handed. -/
theorem length_warmProbes_le_of_budget {adversary : Adversary} {q : Nat}
    (hbudget : HasTotalBudget adversary q)
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk) (publicSeed : Digest)
    (availableAt : QueryCache HashSpec → Node → Prop) (table : Cells × Padding)
    (state : HandlerState) (hstate : state.1 = walk.2) (hstart : state.2.1 = [])
    {result : Outcome × HandlerState}
    (hresult : result ∈ support
      ((simulateQ (lazyProgram publicSeed availableAt table)
        (StrippedGame.strippedAfterSeeds adversary walk.1.1 walk.2)).run state)) :
    (warmProbes walk.2 result.2.2.1).length ≤ q - 2 ^ subtreeHeight := by
  have hbound := warmCount_add_pow_le_of_budget hbudget hwalk publicSeed availableAt table state
    hstate hstart hresult
  rw [length_warmProbes]
  omega

/-! ## The record the half pays for

The claims the forgery makes are not probes the run issued, so they are appended rather than
counted: one entry per claimed cell, read at the cache the run ends with, which is the state at
which every signature has been issued and so the state the extraction's unavailability is
stated against. Their number is a constant, and it is paid out of what key generation spent. -/

/-- One entry per cell the forgery claims, read at the cache the run ends with. -/
def claimedEntries [HasQuery HashSpec Id] (publicSeed : Digest) (cache : QueryCache HashSpec)
    (pk : PublicKey)
    (message : Bytes) (parsed : Signature) : List (Bytes × QueryCache HashSpec) :=
  (ClaimedProbes.claimedCandidatesOf publicSeed cache pk message parsed).map
    fun input => (input, cache)

theorem length_claimedEntries [HasQuery HashSpec Id] (publicSeed : Digest)
    (cache : QueryCache HashSpec) (pk : PublicKey) (message : Bytes) (parsed : Signature) :
    (claimedEntries publicSeed cache pk message parsed).length = 259 := by
  rw [claimedEntries, List.length_map, ClaimedProbes.length_claimedCandidatesOf]

/-- **The whole record the charge is handed fits the budget.** The probes the table answers cost
the work the game charged, which the budget bounds by `q` less key generation's spend; the
forgery's own claims cost their own number, which is a constant. -/
theorem length_record_le_of_budget [HasQuery HashSpec Id] {adversary : Adversary} {q : Nat}
    (hbudget : HasTotalBudget adversary q)
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk) (publicSeed : Digest)
    (availableAt : QueryCache HashSpec → Node → Prop) (table : Cells × Padding)
    (state : HandlerState) (hstate : state.1 = walk.2) (hstart : state.2.1 = [])
    {result : Outcome × HandlerState}
    (hresult : result ∈ support
      ((simulateQ (lazyProgram publicSeed availableAt table)
        (StrippedGame.strippedAfterSeeds adversary walk.1.1 walk.2)).run state))
    (pk : PublicKey) (message : Bytes) (parsed : Signature) :
    (warmProbes walk.2 result.2.2.1 ++
      claimedEntries walk.1.1.2.2 result.2.1 pk message parsed).length ≤
      (q - 2 ^ subtreeHeight) + 259 := by
  have hbound := length_warmProbes_le_of_budget hbudget hwalk publicSeed availableAt table state
    hstate hstart hresult
  rw [List.length_append, length_claimedEntries]
  omega

end SlhDsaSecurity.WarmProbes
