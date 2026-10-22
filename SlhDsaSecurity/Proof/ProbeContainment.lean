import SlhDsaSecurity.Proof.RedrawCell
import SlhDsaSecurity.Proof.SignerRandomiser
import SlhDsaSecurity.Proof.SharedJoin
import SlhDsaSecurity.Proof.KeygenValue
import SlhDsaSecurity.Proof.ServedBridge

/-!
# The probes the charge weighs are the run's own recorded queries

The input half's weight counts the distinct probes that aim at a cell, and the budget pays for
it out of the record's aiming part. What has to be proved is a containment: every aiming probe
the handler records is one the run's record holds. The adversary's and the verifier's queries
are recorded by construction; what needs an argument is that the **honest phase contributes
none**, since its probes reach the handler and are recorded by nobody.

**Stripping disposes of its canonical probes for free.** `StrippedGame.strippedKeygen` and
`strippedSign` answer from the walk's table inside the computation, so a canonical probe never
reaches the handler at all. Key generation therefore contributes nothing, by
`HonestProbes.probes_keygenInternal`; the signer contributes only what the table cannot answer,
which by `SignerRandomiser.probes_signInternalAt` is its randomiser and its message digest, and
`RedrawCell.locate_randomizerInput` and `locate_messageInput` show those aim nowhere.

**The cache a probes statement is read at is the whole of the difficulty, for the fourth time in
this development.** `HonestProbes.Probes` quantifies over `CacheReplay.QueriesUnder cache`,
which follows the *replay* path at `cache`: the path the computation takes when every answer is
read out of that cache. A stripped run takes neither the replay path at the walk's table — it
asks the oracle wherever the table is silent — nor the replay path at the handler's own cache,
which does not hold the table's entries. It takes the replay path at their **union**, which is
`RedrawCell.unionCache` and is the game's own cache. So that is the cache every statement here
is read at, and `queriesUnder_strip` is the step that gets there: at a cache extending the one
stripping answers from, a probe of the stripped computation is a probe of the original.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.ProbeContainment

open Security CacheReplay HonestProbes CanonicalGraph

/-! ## Stripping does not change what a computation consults

The two paths agree once the cache they are read at holds what stripping answered from: where
the table answers, the replayed answer is the table's, and where it does not, both continue with
the same replayed value. -/

/-- **A probe of a stripped computation is a probe of the computation**, read at any cache
extending the one stripping answers from. -/
theorem queriesUnder_strip {α : Type} (computation : OracleComp HashSpec α)
    (cache current : QueryCache HashSpec)
    (hextends : ∀ (input : Bytes) (value : HashOutput),
      cache input = some value → current input = some value)
    (probe : Bytes)
    (hprobe : QueriesUnder current (simulateQ (StripCached.stripImpl cache) computation) probe) :
    QueriesUnder current computation probe := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    rw [simulateQ_pure] at hprobe
    exact absurd hprobe (by rintro ⟨⟩)
  | query_bind input next ih =>
    have hstripped : simulateQ (StripCached.stripImpl cache)
        (liftM (OracleSpec.query input) : OracleComp HashSpec HashOutput) =
        StripCached.stripImpl cache input := by simp
    rw [simulateQ_bind, hstripped] at hprobe
    cases hcache : cache input with
    | some value =>
      rw [show StripCached.stripImpl cache input = (pure value : OracleComp HashSpec HashOutput)
          from by simp [StripCached.stripImpl, hcache], pure_bind] at hprobe
      refine QueriesUnder.tail input probe next ?_
      rw [show replay current input = value from by
        simp [replay, hextends input value hcache]]
      exact ih value hprobe
    | none =>
      rw [show StripCached.stripImpl cache input =
          (liftM (OracleSpec.query input) : OracleComp HashSpec HashOutput) from by
        simp [StripCached.stripImpl, hcache]] at hprobe
      rcases HonestProbes.queriesUnder_query_bind_cases hprobe with rfl | htail
      · exact QueriesUnder.head probe next
      · exact QueriesUnder.tail input probe next (ih _ htail)

/-! ## What the honest phase consults, at the game's cache -/

/-- **Key generation's probes are canonical**, read at any cache. -/
theorem canonical_of_strippedKeygen_probe (warm current : QueryCache HashSpec)
    (hextends : ∀ (input : Bytes) (value : HashOutput),
      warm input = some value → current input = some value)
    (sds : Digest × Digest × Digest) (probe : Bytes)
    (hprobe : QueriesUnder current
      (simulateQ (StripCached.stripImpl warm)
        (Scheme.keygenInternal (m := OracleComp HashSpec) sds.1 sds.2.1 sds.2.2)) probe) :
    Canonical sds.2.2 (replayCells current sds.1 sds.2.2) probe :=
  probes_keygenInternal current sds.1 sds.2.1 sds.2.2 probe
    (queriesUnder_strip _ warm current hextends probe hprobe)

/-- What the honest signer may consult: a canonical input, its request's randomiser input, or
its own message digest's input. -/
def SignerProbe (current : QueryCache HashSpec) (sk : SecretKey) (probe : Bytes) : Prop :=
  Canonical sk.publicKey.seed (replayCells current sk.seed sk.publicKey.seed) probe ∨
    (∃ framed : Bytes, probe = Hashing.randomizerInput sk.prf sk.publicKey.seed framed) ∨
      ∃ (randomizer : Digest) (message : Bytes),
        probe = Hashing.messageInput randomizer sk.publicKey message

/-- **The signer consults only those three.** Its first query is the randomiser's, and
`SignerRandomiser.probes_signInternalAt` settles the rest. -/
theorem probes_sign (current : QueryCache HashSpec) (sk : SecretKey) (request : Message) :
    Probes current (Scheme.sign (m := OracleComp HashSpec) sk request)
      (SignerProbe current sk) := by
  rw [Scheme.sign]
  cases hframe : request.frame with
  | none => exact probes_pure current none _
  | some framed =>
    show Probes current (Scheme.signInternal (m := OracleComp HashSpec) sk framed >>=
      fun signature => pure (some signature.toBytes)) _
    rw [SignerRandomiser.signInternal_eq, bind_assoc, Hashing.randomizer]
    refine probes_shortHash current _ _ _
      (Or.inr (Or.inl ⟨framed, rfl⟩)) ?_
    refine probes_bind current _ _ _ _ rfl ?_ (probes_pure current _ _)
    exact fun probe hprobe =>
      (SignerRandomiser.probes_signInternalAt current _ sk framed probe hprobe).imp id
        fun hdigest => Or.inr ⟨_, framed, hdigest⟩


/-! ## The honest phase's probes, at the game's cache

The game's cache is the table's entries with whatever the handler has drawn beside them, which
is `RedrawCell.unionCache`; it extends the entries stripping answers from, so `queriesUnder_strip`
applies, and the cells it replays are the table's own. So a canonical probe is one the table
answers — which stripping never forwards — and what reaches the handler is the randomiser and
the digest, neither of which aims at a cell. -/

/-- **The table answers every canonical input.** -/
theorem openCache_canonical_ne_none (publicSeed : Digest) (table : Cells × Padding)
    (parent : StructuralNode) :
    OpenCache.openCache publicSeed (fun _ => True) table
      (canonicalInput publicSeed table.1 parent) ≠ none := by
  rw [RedrawCell.openCache_total, Programming.cacheFrom_lookup,
    if_pos (Programming.mem_order parent)]
  simp

/-- **The stripped key generation forwards nothing at all.** Every input it consults is
canonical, and the table answers all of those. -/
theorem no_cold_strippedKeygen_probe (publicSeed : Digest) (table : Cells × Padding)
    (cache : QueryCache HashSpec) (sds : Digest × Digest × Digest)
    (hseed : sds.1 = table.1 Node.secretSeed) (hpublic : sds.2.2 = publicSeed) (probe : Bytes)
    (hprobe : QueriesUnder (RedrawCell.unionCache publicSeed table cache)
      (simulateQ (StripCached.stripImpl (OpenCache.openCache publicSeed (fun _ => True) table))
        (Scheme.keygenInternal (m := OracleComp HashSpec) sds.1 sds.2.1 sds.2.2)) probe)
    (hcold : OpenCache.openCache publicSeed (fun _ => True) table probe = none) : False := by
  have hextends : ∀ (input : Bytes) (value : HashOutput),
      OpenCache.openCache publicSeed (fun _ => True) table input = some value →
        RedrawCell.unionCache publicSeed table cache input = some value :=
    fun input value hvalue =>
      RedrawCell.unionCache_of_open publicSeed table cache input value hvalue
  obtain ⟨parent, hparent⟩ := probes_keygenInternal
    (RedrawCell.unionCache publicSeed table cache) sds.1 sds.2.1 sds.2.2 probe
    (queriesUnder_strip _ _ _ hextends probe hprobe)
  rw [hpublic, hseed, RedrawCell.replayCells_unionCache publicSeed table cache] at hparent
  exact openCache_canonical_ne_none publicSeed table parent (hparent ▸ hcold)

/-- **A probe the stripped signer forwards aims at no cell.** Its canonical probes are answered
by the table and never forwarded; what is left is its randomiser's input, which opens with
`SK.prf`, and its digest's, which would make the public key spell an address. Both are the
walk's own coincidences, and `Target.GoodWalk` is the absence of them. -/
theorem not_aims_of_strippedSign_probe (publicSeed : Digest) (table : Cells × Padding)
    (cache : QueryCache HashSpec) (sk : SecretKey)
    (hseed : sk.seed = table.1 Node.secretSeed) (hpk : sk.publicKey.seed = publicSeed)
    (hprf : sk.prf ≠ publicSeed)
    (hpublic : ¬ HashSeparation.Possible (sk.publicKey.seed, sk.publicKey.root))
    (request : Message) (probe : Bytes)
    (hprobe : QueriesUnder (RedrawCell.unionCache publicSeed table cache)
      (simulateQ (StripCached.stripImpl (OpenCache.openCache publicSeed (fun _ => True) table))
        (Scheme.sign (m := OracleComp HashSpec) sk request)) probe)
    (hcold : OpenCache.openCache publicSeed (fun _ => True) table probe = none) :
    ¬ RedrawCell.AimsSomewhere publicSeed probe := by
  have hextends : ∀ (input : Bytes) (value : HashOutput),
      OpenCache.openCache publicSeed (fun _ => True) table input = some value →
        RedrawCell.unionCache publicSeed table cache input = some value :=
    fun input value hvalue =>
      RedrawCell.unionCache_of_open publicSeed table cache input value hvalue
  have hcases := probes_sign (RedrawCell.unionCache publicSeed table cache) sk request probe
    (queriesUnder_strip _ _ _ hextends probe hprobe)
  rcases hcases with hcanonical | ⟨framed, rfl⟩ | ⟨randomizer, message, rfl⟩
  · obtain ⟨parent, hparent⟩ := hcanonical
    rw [hpk, hseed, RedrawCell.replayCells_unionCache publicSeed table cache] at hparent
    exact absurd (hparent ▸ hcold) (openCache_canonical_ne_none publicSeed table parent)
  · rw [RedrawCell.AimsSomewhere, hpk]
    simp [RedrawCell.locate_randomizerInput publicSeed sk.prf publicSeed framed hprf]
  · rw [RedrawCell.AimsSomewhere]
    simp [RedrawCell.locate_messageInput publicSeed randomizer sk.publicKey message hpublic]


/-! ## What the handler records while the honest phase runs

The per-probe facts above are about what a computation *consults*, read along the replay path at
a cache; the handler's record holds what a **run** forwarded. `strip_probes_queriesUnder` is the
bridge, and it is the `laterCache` pattern once more: the statement is read at any cache
extending both the table's entries and the handler's own, because that is the only cache at
which the run's answers and the replayed ones agree — the table's where the table answered, the
handler's where it drew. -/

open scoped Classical in
/-- **A hash step leaves its own input cached.** -/
theorem lazyProgram_hash_cached (publicSeed : Digest)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (input : Bytes) (state : OpenCache.HandlerState)
    (z : OracleWorld.Range (Sum.inr input) × OpenCache.HandlerState)
    (hz : z ∈ support (((OpenCache.lazyProgram publicSeed availableAt table)
      (Sum.inr input)).run state)) : z.2.1.cache input = some z.1 := by
  classical
  have hbind : z ∈ support
      ((match state.1.cache input with
        | some cached => (pure (cached, state.1) : ProbComp _)
        | none =>
          match OpenCache.openCache publicSeed (availableAt state.1) table input with
          | some answer => pure (answer, HandlerCarrier.cacheAnswer state.1 input answer)
          | none =>
            (fun answer => (answer, HandlerCarrier.cacheAnswer state.1 input answer)) <$>
              ($ᵗ HashOutput : ProbComp HashOutput)) >>= fun step =>
        (pure (step.1, (step.2, state.2.1 ++ [(input, state.1)], state.2.2 + 1)) :
          ProbComp _)) := hz
  rw [mem_support_bind_iff] at hbind
  obtain ⟨step, hstep, hpure⟩ := hbind
  rw [support_pure, Set.mem_singleton_iff] at hpure
  rw [show z.1 = step.1 from by rw [hpure], show z.2.1 = step.2 from by rw [hpure]]
  cases hcached : state.1.cache input with
  | some cached =>
    simp only [hcached, support_pure, Set.mem_singleton_iff] at hstep
    rw [hstep]
    exact hcached
  | none =>
    cases hopen : OpenCache.openCache publicSeed (availableAt state.1) table input with
    | some answer =>
      simp only [hcached, hopen, support_pure, Set.mem_singleton_iff] at hstep
      rw [hstep]
      exact QueryCache.cacheQuery_self _ _ _
    | none =>
      simp only [hcached, hopen, support_map] at hstep
      obtain ⟨answer, -, hanswer⟩ := hstep
      rw [← hanswer]
      exact QueryCache.cacheQuery_self _ _ _


open scoped Classical in
/-- **A probe the handler records while a stripped hash-only computation runs is one that
computation consults.** The statement is read at any cache extending both what stripping answers
from and what the handler ends with, because that is the only cache at which the run's answers
and the replayed ones agree: the table's where the table answered, the handler's where it drew.
-/
theorem strip_probes_queriesUnder {α : Type} (publicSeed : Digest)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (warm : QueryCache HashSpec) (computation : OracleComp HashSpec α) :
    ∀ (state : OpenCache.HandlerState) (z : α × OpenCache.HandlerState),
      z ∈ support ((simulateQ (OpenCache.lazyProgram publicSeed availableAt table)
        (OracleComp.liftComp (simulateQ (StripCached.stripImpl warm) computation)
          OracleWorld)).run state) →
      ∀ later : QueryCache HashSpec,
        (∀ (input : Bytes) (value : HashOutput), warm input = some value →
          later input = some value) →
        (∀ (input : Bytes) (value : HashOutput), warm input = none →
          z.2.1.cache input = some value → later input = some value) →
        ∃ added : List (Bytes × HandlerCarrier.State),
          z.2.2.1 = state.2.1 ++ added ∧
            ∀ entry ∈ added,
              QueriesUnder later (simulateQ (StripCached.stripImpl warm) computation) entry.1 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state z hz later _ _
    rw [simulateQ_pure, OracleComp.liftComp_pure, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    exact ⟨[], by rw [show z.2 = state from by rw [hz], List.append_nil], by simp⟩
  | query_bind input next ih =>
    intro state z hz later hwarm hfinal
    have hstripped : simulateQ (StripCached.stripImpl warm)
        (liftM (OracleSpec.query input) : OracleComp HashSpec HashOutput) =
        StripCached.stripImpl warm input := by simp
    rw [simulateQ_bind, hstripped] at hz
    cases hcache : warm input with
    | some value =>
      rw [show StripCached.stripImpl warm input = (pure value : OracleComp HashSpec HashOutput)
          from by simp [StripCached.stripImpl, hcache], pure_bind] at hz
      obtain ⟨added, hadded, hprobes⟩ := ih value state z hz later hwarm hfinal
      refine ⟨added, hadded, fun entry hentry => ?_⟩
      rw [simulateQ_bind, hstripped,
        show StripCached.stripImpl warm input = (pure value : OracleComp HashSpec HashOutput)
          from by simp [StripCached.stripImpl, hcache], pure_bind]
      exact hprobes entry hentry
    | none =>
      rw [show StripCached.stripImpl warm input =
          (liftM (OracleSpec.query input) : OracleComp HashSpec HashOutput) from by
        simp [StripCached.stripImpl, hcache]] at hz
      have hcold : simulateQ (StripCached.stripImpl warm)
          (liftM (OracleSpec.query input) >>= next) =
          (liftM (OracleSpec.query input) : OracleComp HashSpec HashOutput) >>= fun answer =>
            simulateQ (StripCached.stripImpl warm) (next answer) := by
        rw [simulateQ_bind, hstripped,
          show StripCached.stripImpl warm input =
            (liftM (OracleSpec.query input) : OracleComp HashSpec HashOutput) from by
          simp [StripCached.stripImpl, hcache]]
      have hz' : z ∈ support ((simulateQ (OpenCache.lazyProgram publicSeed availableAt table)
          (liftM (OracleWorld.query (Sum.inr input)) >>=
            fun answer : HashOutput => OracleComp.liftComp
              (simulateQ (StripCached.stripImpl warm) (next answer)) OracleWorld)).run state) := hz
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz'
      obtain ⟨step, hstepRun, hrest⟩ := hz'
      have hrecord : step.2.2.1 = state.2.1 ++ [(input, state.1)] :=
        ChargedProbe.lazyProgram_step_inr publicSeed availableAt table input state step hstepRun
      have hcached : step.2.1.cache input = some step.1 :=
        lazyProgram_hash_cached publicSeed availableAt table input state step hstepRun
      have hpersists : HandlerCarrier.Grows step.2.1 z.2.1 :=
        CacheAvailability.lazyProgram_run_persists publicSeed availableAt table _ step.2 z hrest
      have hreplay : replay later input = step.1 := by
        simp [replay, hfinal input step.1 hcache (hpersists.1 input step.1 hcached)]
      obtain ⟨added, hadded, hprobes⟩ := ih step.1 step.2 z hrest later hwarm hfinal
      refine ⟨(input, state.1) :: added, by rw [hadded, hrecord, List.append_assoc]; rfl, ?_⟩
      intro entry hentry
      rw [hcold]
      rcases List.mem_cons.mp hentry with hhead | htail
      · rw [hhead]
        exact QueriesUnder.head _ _
      · exact QueriesUnder.tail input entry.1 _ (by rw [hreplay]; exact hprobes entry htail)


/-! ## The honest phase appends nothing that aims

The two halves meet here: what the handler records while the honest phase runs is what that
phase consults, and what it consults that the table does not answer aims nowhere.

**No compatibility between the two caches is needed, and that is a fact about the argument's
shape rather than an economy.** The side condition on the cache a probe statement is read at is
used only where the table is *silent* — which is exactly where a probe is forwarded to the
handler at all — and `RedrawCell.unionCache` defers to the handler's own cache precisely there.
So the condition discharges itself, `RedrawCell.Compatible` never appears, and the containment
holds at **any** availability: it never compares what the handler answered with what the table
would have. Had the hypothesis merely been proved instead of removed, that would not be
visible. -/

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 1000000 in
/-- **A run of the stripped signer appends no aiming probe to the record.** -/
theorem strippedSign_adds_no_aiming (publicSeed : Digest)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (sk : SecretKey) (hseed : sk.seed = table.1 Node.secretSeed)
    (hpk : sk.publicKey.seed = publicSeed) (hprf : sk.prf ≠ publicSeed)
    (hpublic : ¬ HashSeparation.Possible (sk.publicKey.seed, sk.publicKey.root))
    (request : Message) (state : OpenCache.HandlerState)
    (z : Option Bytes × OpenCache.HandlerState)
    (hz : z ∈ support ((simulateQ (OpenCache.lazyProgram publicSeed availableAt table)
      (StrippedGame.strippedSign (OpenCache.openCache publicSeed (fun _ => True) table) sk
        request)).run state))
    :
    ∃ added : List (Bytes × HandlerCarrier.State),
      z.2.2.1 = state.2.1 ++ added ∧
        ∀ entry ∈ added, ¬ RedrawCell.AimsSomewhere publicSeed entry.1 := by
  obtain ⟨added, hadded, hprobes⟩ := strip_probes_queriesUnder publicSeed availableAt table
    (OpenCache.openCache publicSeed (fun _ => True) table)
    (Scheme.sign (m := OracleComp HashSpec) sk request) state z hz
    (RedrawCell.unionCache publicSeed table z.2.1.cache)
    (fun input value hvalue =>
      RedrawCell.unionCache_of_open publicSeed table z.2.1.cache input value hvalue)
    (fun input value hnone _ =>
      (RedrawCell.unionCache_of_none publicSeed table z.2.1.cache input hnone).symm ▸ by
        assumption)
  refine ⟨added, hadded, fun entry hentry => ?_⟩
  by_cases hcold : OpenCache.openCache publicSeed (fun _ => True) table entry.1 = none
  · exact not_aims_of_strippedSign_probe publicSeed table z.2.1.cache sk hseed hpk hprf hpublic
      request entry.1 (hprobes entry hentry) hcold
  · exact absurd (StripCached.queriesUnder_strip_none
      (Scheme.sign (m := OracleComp HashSpec) sk request) _ _ entry.1 (hprobes entry hentry))
      hcold

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 1000000 in
/-- **A run of the stripped key generation appends nothing at all.** -/
theorem strippedKeygen_adds_nothing (publicSeed : Digest)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (sds : Digest × Digest × Digest) (hseed : sds.1 = table.1 Node.secretSeed)
    (hpublic : sds.2.2 = publicSeed) (state : OpenCache.HandlerState)
    (z : (SecretKey × PublicKey) × OpenCache.HandlerState)
    (hz : z ∈ support ((simulateQ (OpenCache.lazyProgram publicSeed availableAt table)
      (StrippedGame.strippedKeygen (OpenCache.openCache publicSeed (fun _ => True) table)
        sds)).run state))
    :
    z.2.2.1 = state.2.1 := by
  obtain ⟨added, hadded, hprobes⟩ := strip_probes_queriesUnder publicSeed availableAt table
    (OpenCache.openCache publicSeed (fun _ => True) table)
    (Scheme.keygenInternal (m := OracleComp HashSpec) sds.1 sds.2.1 sds.2.2) state z hz
    (RedrawCell.unionCache publicSeed table z.2.1.cache)
    (fun input value hvalue =>
      RedrawCell.unionCache_of_open publicSeed table z.2.1.cache input value hvalue)
    (fun input value hnone _ =>
      (RedrawCell.unionCache_of_none publicSeed table z.2.1.cache input hnone).symm ▸ by
        assumption)
  rw [hadded, show added = [] from ?_, List.append_nil]
  refine List.eq_nil_iff_forall_not_mem.mpr fun entry hentry => ?_
  exact no_cold_strippedKeygen_probe publicSeed table z.2.1.cache sds hseed hpublic entry.1
    (hprobes entry hentry)
    (StripCached.queriesUnder_strip_none
      (Scheme.keygenInternal (m := OracleComp HashSpec) sds.1 sds.2.1 sds.2.2) _ _ entry.1
      (hprobes entry hentry))


/-! ## Counting the aiming probes against the record's aiming part

The weight is a count of the handler's list; the budget pays out of the run's recorded multiset.
Both sides are counted by the same test, and a step moves them together: a hash call appends one
probe and records one input, and a probe that aims is an input that aims. -/

open scoped Classical in
/-- The aiming probes a handler's record holds. -/
noncomputable def aimCount (publicSeed : Digest)
    (record : List (Bytes × HandlerCarrier.State)) : Nat :=
  record.countP (fun entry => decide (RedrawCell.AimsSomewhere publicSeed entry.1))

open scoped Classical in
/-- The aiming inputs a run's record holds. -/
noncomputable def recordAim (publicSeed : Digest) (record : Multiset Bytes) : Nat :=
  Multiset.card (record.filter (RedrawCell.AimsSomewhere publicSeed))

open scoped Classical in
theorem aimCount_append (publicSeed : Digest)
    (left right : List (Bytes × HandlerCarrier.State)) :
    aimCount publicSeed (left ++ right) =
      aimCount publicSeed left + aimCount publicSeed right := List.countP_append

open scoped Classical in
theorem recordAim_add (publicSeed : Digest) (left right : Multiset Bytes) :
    recordAim publicSeed (left + right) =
      recordAim publicSeed left + recordAim publicSeed right := by
  rw [recordAim, recordAim, recordAim, Multiset.filter_add, Multiset.card_add]

open scoped Classical in
/-- **A step appends exactly what it records**, counted by the aiming test. -/
theorem aimCount_step (publicSeed : Digest)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (queried : OracleWorld.Domain) (state : OpenCache.HandlerState)
    (z : OracleWorld.Range queried × OpenCache.HandlerState)
    (hz : z ∈ support
      (((OpenCache.lazyProgram publicSeed availableAt table) queried).run state)) :
    aimCount publicSeed z.2.2.1 =
      aimCount publicSeed state.2.1 +
        recordAim publicSeed (RecordedQueries.recordOf queried) := by
  classical
  rcases queried with coin | input
  · rw [OpenCache.lazyProgram_run_inl, mem_support_bind_iff] at hz
    obtain ⟨value, -, hpure⟩ := hz
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [show z.2 = state from by rw [hpure]]
    simp [RecordedQueries.recordOf, recordAim]
  · rw [ChargedProbe.lazyProgram_step_inr publicSeed availableAt table input state z hz,
      aimCount_append]
    refine congrArg _ ?_
    by_cases haims : RedrawCell.AimsSomewhere publicSeed input
    · rw [aimCount, List.countP_singleton, if_pos (by simpa using haims), recordAim,
        show RecordedQueries.recordOf (Sum.inr input) = ({input} : Multiset Bytes) from rfl,
        Multiset.filter_singleton, if_pos haims]
      rfl
    · rw [aimCount, List.countP_singleton, if_neg (by simpa using haims), recordAim,
        show RecordedQueries.recordOf (Sum.inr input) = ({input} : Multiset Bytes) from rfl,
        Multiset.filter_singleton, if_neg haims]
      rfl


open scoped Classical in
/-- **One of the adversary's own queries appends exactly what it records.** -/
theorem aimCount_recordedAdversaryImpl (publicSeed : Digest)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (queried : OracleWorld.Domain) (log : SigningLog) (state : OpenCache.HandlerState)
    (outer : ((OracleWorld.Range queried × Multiplicative RecordedQueries.Tally) × SigningLog) ×
      OpenCache.HandlerState)
    (houter : outer ∈ support ((simulateQ (OpenCache.lazyProgram publicSeed availableAt table)
      ((WriterT.run (RecordedQueries.recordedAdversaryImpl queried)).run log)).run state)) :
    aimCount publicSeed outer.2.2.1 =
      aimCount publicSeed state.2.1 +
        recordAim publicSeed (Multiplicative.toAdd outer.1.1.2).2 := by
  classical
  rw [RecordedQueries.run_recordedAdversaryImpl, simulateQ_map, StateT.run_map,
    support_map] at houter
  obtain ⟨inner, hinner, heq⟩ := houter
  rw [simulateQ_spec_query] at hinner
  rw [show outer.1.1.2 = Multiplicative.ofAdd
      ((Counts.single .hash (hashCost queried) : Counts), RecordedQueries.recordOf queried) from by
      rw [← heq],
    show outer.2 = inner.2 from by rw [← heq], toAdd_ofAdd]
  exact aimCount_step publicSeed availableAt table queried state inner hinner

open scoped Classical in
/-- **A signing request appends nothing that aims, and records nothing.** -/
theorem aimCount_recordedSigningOracle (publicSeed : Digest)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (sk : SecretKey) (hseed : sk.seed = table.1 Node.secretSeed)
    (hpk : sk.publicKey.seed = publicSeed) (hprf : sk.prf ≠ publicSeed)
    (hpublic : ¬ HashSeparation.Possible (sk.publicKey.seed, sk.publicKey.root))
    (request : Message) (log : SigningLog) (state : OpenCache.HandlerState)
    (outer : ((Option Bytes × Multiplicative RecordedQueries.Tally) × SigningLog) ×
      OpenCache.HandlerState)
    (houter : outer ∈ support ((simulateQ (OpenCache.lazyProgram publicSeed availableAt table)
      ((WriterT.run (RecordedQueries.recordedSigningOracle
        (StrippedGame.strippedSign (OpenCache.openCache publicSeed (fun _ => True) table) sk)
        request)).run log)).run state))
    :
    aimCount publicSeed outer.2.2.1 = aimCount publicSeed state.2.1 := by
  classical
  rw [RecordedQueries.run_recordedSigningOracle, simulateQ_bind, StateT.run_bind,
    mem_support_bind_iff] at houter
  obtain ⟨step, hstep, hrest⟩ := houter
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hrest
  rw [show outer.2 = step.2 from by rw [hrest]]
  obtain ⟨added, hadded, hprobes⟩ := strippedSign_adds_no_aiming publicSeed availableAt table sk
    hseed hpk hprf hpublic request state step hstep
  rw [hadded, aimCount_append, show aimCount publicSeed added = 0 from ?_, Nat.add_zero]
  refine List.countP_eq_zero.mpr fun entry hentry => ?_
  simpa using hprobes entry hentry


set_option maxHeartbeats 1000000 in
set_option linter.constructorNameAsVariable false in
open scoped Classical in
/-- **The adversary's phase appends at most what it records.** Its own queries append exactly
what they record; its signing requests append nothing that aims and record nothing. -/
theorem aimCount_adversary (publicSeed : Digest)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (sk : SecretKey) (hseed : sk.seed = table.1 Node.secretSeed)
    (hpk : sk.publicKey.seed = publicSeed) (hprf : sk.prf ≠ publicSeed)
    (hpublic : ¬ HashSeparation.Possible (sk.publicKey.seed, sk.publicKey.root))
    {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (log : SigningLog) (state : OpenCache.HandlerState)
      (result : ((α × Multiplicative RecordedQueries.Tally) × SigningLog) ×
        OpenCache.HandlerState),
      result ∈ support ((simulateQ (OpenCache.lazyProgram publicSeed availableAt table)
        ((WriterT.run (simulateQ (RecordedQueries.recordedAdversaryImpl +
          RecordedQueries.recordedSigningOracle
            (StrippedGame.strippedSign (OpenCache.openCache publicSeed (fun _ => True) table) sk))
          computation)).run log)).run state) →
        aimCount publicSeed result.2.2.1 ≤
          aimCount publicSeed state.2.1 +
            recordAim publicSeed (Multiplicative.toAdd result.1.1.2).2 := by
  classical
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro log state result hmem
    rw [simulateQ_pure, show ((WriterT.run (pure value :
          RecordedQueries.RecordedRun α)).run log) =
        (pure ((value, (1 : Multiplicative RecordedQueries.Tally)), log) :
          OracleComp OracleWorld
            ((α × Multiplicative RecordedQueries.Tally) × SigningLog)) from rfl,
      simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [show result.2 = state from by rw [hmem]]
    exact Nat.le_add_right _ _
  | query_bind queried next ih =>
    intro log state result hmem
    rw [simulateQ_bind, simulateQ_spec_query, RecordedQueries.run_writer_bind, simulateQ_bind,
      StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨outer, houter, hrest⟩ := hmem
    rw [simulateQ_map, StateT.run_map, support_map] at hrest
    obtain ⟨inner, hinner, heq⟩ := hrest
    have htail := ih outer.1.1.1 outer.1.2 outer.2 inner hinner
    have hhead : aimCount publicSeed outer.2.2.1 ≤
        aimCount publicSeed state.2.1 +
          recordAim publicSeed (Multiplicative.toAdd outer.1.1.2).2 := by
      rcases queried with world | request
      · exact le_of_eq (aimCount_recordedAdversaryImpl publicSeed availableAt table world log
          state outer houter)
      · rw [aimCount_recordedSigningOracle publicSeed availableAt table sk hseed hpk hprf hpublic
          request log state outer houter]
        exact Nat.le_add_right _ _
    have hvalue : result.1.1.2 = outer.1.1.2 * inner.1.1.2 := by
      rw [← congrArg (fun z => z.1.1.2) heq]
    have hstate : result.2 = inner.2 := by rw [← congrArg Prod.snd heq]
    rw [hstate, hvalue, toAdd_mul,
      show (Multiplicative.toAdd outer.1.1.2 + Multiplicative.toAdd inner.1.1.2).2 =
        (Multiplicative.toAdd outer.1.1.2).2 + (Multiplicative.toAdd inner.1.1.2).2 from rfl,
      recordAim_add, ← Nat.add_assoc]
    exact le_trans htail (Nat.add_le_add_right hhead _)


set_option maxHeartbeats 1000000 in
set_option linter.constructorNameAsVariable false in
open scoped Classical in
/-- **An instrumentation that records every hash call appends exactly what it records.** This is
the verifier's phase: it is handled by nobody, so every input it consults reaches the handler
and is recorded in the same step. -/
theorem aimCount_countRecorded (publicSeed : Digest)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    {α : Type} (computation : OracleComp OracleWorld α) :
    ∀ (state : OpenCache.HandlerState)
      (result : (α × RecordedQueries.Tally) × OpenCache.HandlerState),
      result ∈ support ((simulateQ (OpenCache.lazyProgram publicSeed availableAt table)
        (RecordedQueries.countRecorded RecordedQueries.verifierCost computation)).run state) →
        aimCount publicSeed result.2.2.1 =
          aimCount publicSeed state.2.1 + recordAim publicSeed result.1.2.2 := by
  classical
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state result hmem
    rw [RecordedQueries.countRecorded_pure, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hmem
    rw [show result.2 = state from by rw [hmem],
      show result.1.2 = (0 : RecordedQueries.Tally) from by rw [hmem]]
    simp [recordAim]
  | query_bind queried next ih =>
    intro state result hmem
    rw [RecordedQueries.countRecorded_query_bind, simulateQ_bind, simulateQ_spec_query,
      StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    rw [simulateQ_map, StateT.run_map, support_map] at hrest
    obtain ⟨inner, hinner, heq⟩ := hrest
    have htail := ih step.1 step.2 inner hinner
    have hhead := aimCount_step publicSeed availableAt table queried state step hstep
    have hvalue : result.1.2 = RecordedQueries.verifierCost queried + inner.1.2 := by
      rw [← congrArg (fun z => z.1.2) heq]
    have hstate : result.2 = inner.2 := by rw [← congrArg Prod.snd heq]
    rw [hstate, htail, hhead, hvalue,
      show (RecordedQueries.verifierCost queried + inner.1.2).2 =
        RecordedQueries.recordOf queried + inner.1.2.2 from rfl,
      recordAim_add, Nat.add_assoc]


attribute [local irreducible] Scheme.keygenInternal Scheme.sign Scheme.verify

set_option maxHeartbeats 4000000 in
set_option linter.constructorNameAsVariable false in
open scoped Classical in
/-- **The whole stripped game appends at most what it records**, counted by the aiming test.
Key generation appends nothing, the adversary's own queries append exactly what they record, its
signing requests append nothing that aims, and the verifier's calls append exactly what they
record. -/
theorem aimCount_recordedAfterSeeds (publicSeed : Digest)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (adversary : Adversary) (sds : Digest × Digest × Digest)
    (hsds : sds.1 = table.1 Node.secretSeed) (hpub : sds.2.2 = publicSeed)
    (sk : SecretKey) (pk : PublicKey)
    (hseed : sk.seed = table.1 Node.secretSeed) (hpk : sk.publicKey.seed = publicSeed)
    (hprf : sk.prf ≠ publicSeed)
    (hpublic : ¬ HashSeparation.Possible (sk.publicKey.seed, sk.publicKey.root))
    (hkeygen : ∀ (inner : OpenCache.HandlerState)
      (keys : (SecretKey × PublicKey) × OpenCache.HandlerState),
      keys ∈ support ((simulateQ (OpenCache.lazyProgram publicSeed availableAt table)
        (StrippedGame.strippedKeygen (OpenCache.openCache publicSeed (fun _ => True) table)
          sds)).run inner) → keys.1 = (sk, pk))
    (state : OpenCache.HandlerState)
    (result : (Outcome × Multiset Bytes) × OpenCache.HandlerState)
    (hmem : result ∈ support ((simulateQ (OpenCache.lazyProgram publicSeed availableAt table)
      (RecordedQueries.recordedAfterSeeds adversary sds
        (OpenCache.openCache publicSeed (fun _ => True) table))).run state)) :
    aimCount publicSeed result.2.2.1 ≤
      aimCount publicSeed state.2.1 + recordAim publicSeed result.1.2 := by
  classical
  unfold RecordedQueries.recordedAfterSeeds at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨keys, hkeys, hmem⟩ := hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨phase, hphase, hmem⟩ := hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨verify, hverify, hmem⟩ := hmem
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
  have hkeygen' := strippedKeygen_adds_nothing publicSeed availableAt table sds hsds hpub
    state keys hkeys
  have hkey := hkeygen state keys hkeys
  have hphase' := aimCount_adversary publicSeed availableAt table sk hseed hpk hprf hpublic
    (adversary.main pk) [] keys.2 phase (by
      rw [show pk = keys.1.2 from by rw [hkey], show sk = keys.1.1 from by rw [hkey]]
      exact hphase)
  have hverify' := aimCount_countRecorded publicSeed availableAt table
    (Scheme.verify pk phase.1.1.1.message phase.1.1.1.signature) phase.2 verify (by
      rw [show pk = keys.1.2 from by rw [hkey]]
      exact hverify)
  rw [show result.2 = verify.2 from by rw [hmem],
    show result.1.2 = (Multiplicative.toAdd phase.1.1.2).2 + verify.1.2.2 from by rw [hmem],
    recordAim_add, hverify']
  rw [hkeygen'] at hphase'
  omega


/-! ## What the charge may take

The weight the charge carries is the **de-duplicated** aiming part of the handler's record, and
the budget pays out of the aiming part of the run's own. The first is at most the second:
de-duplicating only shortens a list, and the count above is an identity rather than a bound, so
nothing accumulates between them. -/

open scoped Classical in
/-- **A de-duplicated filter is no longer than the filter.** -/
theorem dedup_filter_length_le (publicSeed : Digest)
    (record : List (Bytes × HandlerCarrier.State)) :
    (record.dedup.filter
        (fun entry => decide (RedrawCell.AimsSomewhere publicSeed entry.1))).length ≤
      aimCount publicSeed record := by
  classical
  rw [aimCount, List.countP_eq_length_filter]
  exact List.Sublist.length_le (List.Sublist.filter _ (List.dedup_sublist _))

set_option maxHeartbeats 4000000 in
open scoped Classical in
/-- **The charge's weight is at most the record's aiming part.** This is the containment, in the
form the charge consumes it: the handler starts with an empty record, so what it accumulates is
what the run records, counted by the same test. -/
theorem weight_le_recordAim (publicSeed : Digest)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (adversary : Adversary) (sds : Digest × Digest × Digest)
    (hsds : sds.1 = table.1 Node.secretSeed) (hpub : sds.2.2 = publicSeed)
    (sk : SecretKey) (pk : PublicKey)
    (hseed : sk.seed = table.1 Node.secretSeed) (hpk : sk.publicKey.seed = publicSeed)
    (hprf : sk.prf ≠ publicSeed)
    (hpublic : ¬ HashSeparation.Possible (sk.publicKey.seed, sk.publicKey.root))
    (hkeygen : ∀ (inner : OpenCache.HandlerState)
      (keys : (SecretKey × PublicKey) × OpenCache.HandlerState),
      keys ∈ support ((simulateQ (OpenCache.lazyProgram publicSeed availableAt table)
        (StrippedGame.strippedKeygen (OpenCache.openCache publicSeed (fun _ => True) table)
          sds)).run inner) → keys.1 = (sk, pk))
    (state : OpenCache.HandlerState) (hstart : state.2.1 = [])
    (result : (Outcome × Multiset Bytes) × OpenCache.HandlerState)
    (hmem : result ∈ support ((simulateQ (OpenCache.lazyProgram publicSeed availableAt table)
      (RecordedQueries.recordedAfterSeeds adversary sds
        (OpenCache.openCache publicSeed (fun _ => True) table))).run state)) :
    (result.2.2.1.dedup.filter
        (fun entry => decide (RedrawCell.AimsSomewhere publicSeed entry.1))).length ≤
      Multiset.card (result.1.2.filter (RedrawCell.AimsSomewhere publicSeed)) := by
  classical
  refine le_trans (dedup_filter_length_le publicSeed result.2.2.1) ?_
  have hbound := aimCount_recordedAfterSeeds publicSeed availableAt table adversary sds hsds hpub
    sk pk hseed hpk hprf hpublic hkeygen state result hmem
  rw [hstart, show aimCount publicSeed [] = 0 from rfl, Nat.zero_add] at hbound
  exact hbound



/-! ## The same, with the keys handed in

The charge reads the game with key generation already replaced by the value the walk's cache
determines, because that is what lets the signer's reads of the table be frozen. The containment
is simpler there, not harder: with no key generation in the computation there is no keygen step
to account for, and the assembly is the adversary's phase and the verifier's. -/

set_option maxHeartbeats 4000000 in
set_option linter.constructorNameAsVariable false in
open scoped Classical in
/-- **The game with its keys handed in appends at most what it records.** -/
theorem aimCount_recordedAfterSeedsAt (publicSeed : Digest)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (adversary : Adversary) (keys : SecretKey × PublicKey)
    (hseed : keys.1.seed = table.1 Node.secretSeed)
    (hpk : keys.1.publicKey.seed = publicSeed) (hprf : keys.1.prf ≠ publicSeed)
    (hpublic : ¬ HashSeparation.Possible (keys.1.publicKey.seed, keys.1.publicKey.root))
    (state : OpenCache.HandlerState)
    (result : (Outcome × Multiset Bytes) × OpenCache.HandlerState)
    (hmem : result ∈ support ((simulateQ (OpenCache.lazyProgram publicSeed availableAt table)
      (KeygenValue.recordedAfterSeedsAt adversary keys
        (OpenCache.openCache publicSeed (fun _ => True) table))).run state)) :
    aimCount publicSeed result.2.2.1 ≤
      aimCount publicSeed state.2.1 + recordAim publicSeed result.1.2 := by
  classical
  unfold KeygenValue.recordedAfterSeedsAt at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨phase, hphase, hmem⟩ := hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨verify, hverify, hmem⟩ := hmem
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
  have hphase' := aimCount_adversary publicSeed availableAt table keys.1 hseed hpk hprf hpublic
    (adversary.main keys.2) [] state phase hphase
  have hverify' := aimCount_countRecorded publicSeed availableAt table
    (Scheme.verify keys.2 phase.1.1.1.message phase.1.1.1.signature) phase.2 verify hverify
  rw [show result.2 = verify.2 from by rw [hmem],
    show result.1.2 = (Multiplicative.toAdd phase.1.1.2).2 + verify.1.2.2 from by rw [hmem],
    recordAim_add, hverify']
  omega

set_option maxHeartbeats 4000000 in
open scoped Classical in
/-- **The charge's weight is at most the record's aiming part**, with the keys handed in. -/
theorem weight_le_recordAim_at (publicSeed : Digest)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (adversary : Adversary) (keys : SecretKey × PublicKey)
    (hseed : keys.1.seed = table.1 Node.secretSeed)
    (hpk : keys.1.publicKey.seed = publicSeed) (hprf : keys.1.prf ≠ publicSeed)
    (hpublic : ¬ HashSeparation.Possible (keys.1.publicKey.seed, keys.1.publicKey.root))
    (state : OpenCache.HandlerState) (hstart : state.2.1 = [])
    (result : (Outcome × Multiset Bytes) × OpenCache.HandlerState)
    (hmem : result ∈ support ((simulateQ (OpenCache.lazyProgram publicSeed availableAt table)
      (KeygenValue.recordedAfterSeedsAt adversary keys
        (OpenCache.openCache publicSeed (fun _ => True) table))).run state)) :
    (result.2.2.1.dedup.filter
        (fun entry => decide (RedrawCell.AimsSomewhere publicSeed entry.1))).length ≤
      Multiset.card (result.1.2.filter (RedrawCell.AimsSomewhere publicSeed)) := by
  classical
  refine le_trans (dedup_filter_length_le publicSeed result.2.2.1) ?_
  have hbound := aimCount_recordedAfterSeedsAt publicSeed availableAt table adversary keys hseed
    hpk hprf hpublic state result hmem
  rw [hstart, show aimCount publicSeed [] = 0 from rfl, Nat.zero_add] at hbound
  exact hbound

/-! ## The export, in the join's vocabulary

**`ProbesIn` is reflexivity here, and the reflexivity is not the argument.** `ProbesIn` takes
the probe list as a function of the join's pair, and this half's list is a feature of the
*handler's state*, which the pair does not carry — so the list this half offers the join **is**
the part, the containment it discharges is trivially true, and all of the content has moved one
slot along, into the weight inequality `weight_le_recordAim` that `hinput_of_probesIn`'s
`hcharge` consumes. A reader who sees `le_refl` here should not conclude that the containment
was free. It was not: it is the whole of this file, and it is proved against the same part.

The other owner of a containment is not in this position — its probe list is a function of a
larger pair, with a forgetting map down to this one — so the two discharge the same obligation
in different places, both soundly. -/

/-- **The aiming part is the same test on both sides.** -/
theorem recordAim_eq_card_recordAiming (pair : SharedJoin.RecordedPair) :
    recordAim pair.1.1.1.2.2 (SharedJoin.recordOf pair) =
      Multiset.card (SharedJoin.recordAiming pair) := rfl

/-- **The containment the join asks of this half.** See the note above: the content is in
`weight_le_recordAim`, not here. -/
theorem probesIn_recordAiming (adversary : Adversary) :
    SharedJoin.ProbesIn SharedJoin.recordAiming SharedJoin.recordAiming adversary :=
  fun _ _ => le_refl _



/-! ## The forgery's claims never stake the secret seed

The half is charged at `RedrawCell.SensitiveOffSeed`, the avenue whose staked cell is not the
secret seed; the seed's own avenue is charged elsewhere and must not be paid for twice. For the
forgery's claims the distinction costs nothing, and structurally rather than by hypothesis:
every claimed candidate is the canonical input of a FORS leaf or a WOTS chain step, whose staked
cell is a **structural** node — a signature carries no claim about the seed. So a sensitive
claim is a sensitive claim off the seed, and the seed term does not arise on this side at all.
-/

/-- **Every claim is the input of a node that stakes a structural cell.** -/
theorem claimedCandidates_cases (publicSeed : Digest) (forsKey : ForsKey)
    (indices : SlhDsaSecurity.Fors.Indices) (signature : Signature)
    (keyAt : Fin layers → WotsKey) (stepAt : Fin layers → Fin chains → Fin (w - 1))
    (candidate : Bytes)
    (hmem : candidate ∈
      GraphStakes.claimedCandidates publicSeed forsKey indices signature keyAt stepAt) :
    ∃ (node : GraphStakes.SensitiveNode) (cell : SensitiveQuery.Cell),
      node.child ≠ Node.secretSeed ∧ GraphStakes.inputOf publicSeed node cell = candidate := by
  rw [GraphStakes.claimedCandidates, List.mem_append] at hmem
  rcases hmem with hfors | hwots
  · obtain ⟨tree, -, htree⟩ := List.mem_map.mp hfors
    exact ⟨GraphStakes.forsLeafNode forsKey (GraphStakes.forsIndex indices tree),
      (signature.fors tree).secret, by simp [GraphStakes.forsLeafNode], htree⟩
  · obtain ⟨layer, -, hlayer⟩ := List.mem_flatMap.mp hwots
    obtain ⟨chain, -, hchain⟩ := List.mem_map.mp hlayer
    exact ⟨GraphStakes.wotsHashNode (keyAt layer) chain (stepAt layer chain),
      ((signature.hypertree layer).wots chain), by simp [GraphStakes.wotsHashNode], hchain⟩

/-- **A sensitive claim is sensitive off the seed.** -/
theorem sensitiveOffSeed_of_claim (publicSeed : Digest)
    (unavailable : HandlerCarrier.State → Node → Prop) (table : Cells)
    (state : HandlerCarrier.State) (candidate : Bytes)
    (hclaim : ∃ (node : GraphStakes.SensitiveNode) (cell : SensitiveQuery.Cell),
      node.child ≠ Node.secretSeed ∧ GraphStakes.inputOf publicSeed node cell = candidate)
    (hsensitive : SensitiveQuery.Sensitive (GraphStakes.stakes publicSeed) unavailable table
      state candidate) :
    RedrawCell.SensitiveOffSeed (GraphStakes.stakes publicSeed) unavailable table state
      candidate := by
  obtain ⟨node, cell, hchild, hinput⟩ := hclaim
  obtain ⟨witness, hunavailable, hwitness⟩ := hsensitive
  have hsame : witness = node :=
    (GraphStakes.inputOf_inj publicSeed (hwitness.trans hinput.symm)).1
  exact ⟨witness, by rw [show (GraphStakes.stakes publicSeed).stake witness =
      witness.child from rfl, hsame]; exact hchild, hunavailable, hwitness⟩





/-! ## From the half's event to the charge's

`RoutedSplit.InputBad` says some claimed candidate is sensitive, with disclosure read from the
**log**; the charge's event says some entry of the half's list is sensitive off the seed, with
disclosure read from the **carrier**. Three facts close the gap, and only the first belongs to
anyone else:

* the two disclosure sets are one, which is what `ServedBridge.ServedAgree` buys;
* a claim is in the half's list, which is `mem_claimsOf`;
* a sensitive claim is sensitive off the seed, which is `sensitiveOffSeed_of_claim` and holds
  because a signature carries no claim about the seed.

The first is isolated as a hypothesis about the *sets* rather than about the runs, so that the
implication can be read without knowing where either came from. -/

/-- **Sensitivity transports along an equality of disclosed sets**, and a claim's sensitivity
transports to the avenue off the seed. -/
theorem sensitiveOffSeed_of_sensitive_sets {StateA : Type} (publicSeed : Digest)
    (revealed : WotsKey → Fin chains → Nat)
    (signedA : StateA → ForsKey → Finset (Fin (forsTrees * 2 ^ forsHeight)))
    (signedB : HandlerCarrier.State → ForsKey → Finset (Fin (forsTrees * 2 ^ forsHeight)))
    (stateA : StateA) (stateB : HandlerCarrier.State)
    (hsets : ∀ key, signedA stateA key = signedB stateB key)
    (cells : Cells) (candidate : Bytes)
    (hclaim : ∃ (node : GraphStakes.SensitiveNode) (cell : SensitiveQuery.Cell),
      node.child ≠ Node.secretSeed ∧ GraphStakes.inputOf publicSeed node cell = candidate)
    (hsensitive : SensitiveQuery.Sensitive (GraphStakes.stakes publicSeed)
      (GraphStakes.unavailableAt revealed signedA) cells stateA candidate) :
    RedrawCell.SensitiveOffSeed (GraphStakes.stakes publicSeed)
      (GraphStakes.unavailableAt revealed signedB) cells stateB candidate := by
  refine sensitiveOffSeed_of_claim publicSeed
    (GraphStakes.unavailableAt revealed signedB) cells stateB candidate hclaim ?_
  obtain ⟨node, hunavailable, hinput⟩ := hsensitive
  refine ⟨node, ?_, hinput⟩
  rw [GraphStakes.unavailableAt] at hunavailable ⊢
  rw [show signedB stateB = signedA stateA from by funext key; rw [hsets key]]
  exact hunavailable

open scoped Classical in
/-- **The two disclosure sets are one**, which is the whole of what the agreement buys. -/
theorem disclosedAt_eq_disclosedByLog [HasQuery HashSpec Id] (pk : PublicKey)
    (carrier : ServingCarrier.Carrier)
    (result : (Outcome × Nat) × QueryCache HashSpec)
    (hagree : ServedBridge.ServedAgree pk carrier result)
    (hcacheLeft : ∀ (input : Bytes) (answer : HashOutput),
      ServingCarrier.cacheOf carrier input = some answer → result.2 input = some answer)
    (hcacheRight : ∀ (input : Bytes) (answer : HashOutput),
      result.2 input = some answer → ServingCarrier.cacheOf carrier input = some answer)
    (key : ForsKey) :
    ServingCarrier.disclosedAt carrier key = ServedLog.disclosedByLog pk result key :=
  Finset.Subset.antisymm
    (ServedBridge.disclosedAt_subset_disclosedByLog pk carrier result hagree.1 hcacheLeft key)
    (ServedBridge.disclosedByLog_subset_disclosedAt pk carrier result hagree.2 hcacheRight key)

/-! ## The claims the charge is handed

The charge takes its list as a function of the run's result and pairs each entry with the
carrier availability is read at, so the half builds its own list rather than growing a
carrier-valued twin of `WarmProbes.claimedEntries`: the list is the half's and nobody else reads
it.

A forgery whose frame or signature does not parse claims nothing, so the list is empty there —
which is sound because `RoutedSplit.InputBad` requires both to parse before it asks anything
else. Its length is `259` when they do and `0` when they do not, so the constant bounds it
either way. -/

open scoped Classical in
/-- The forgery's claimed candidates, paired with the carrier they are read at. -/
noncomputable def claimsOf [HasQuery HashSpec Id] (publicSeed : Digest)
    (pk : PublicKey) (forgery : Forgery) (carrier : HandlerCarrier.State) :
    List (Bytes × HandlerCarrier.State) :=
  match forgery.message.frame, Signature.fromBytes? forgery.signature with
  | some message, some parsed =>
      (ClaimedProbes.claimedCandidatesOf publicSeed carrier.cache pk message parsed).map
        fun input => (input, carrier)
  | _, _ => []

open scoped Classical in
/-- **Every claim is read at the carrier the run ends with.** -/
theorem claimsOf_carrier [HasQuery HashSpec Id] (publicSeed : Digest)
    (pk : PublicKey) (forgery : Forgery)
    (carrier : HandlerCarrier.State) (entry : Bytes × HandlerCarrier.State)
    (hentry : entry ∈ claimsOf publicSeed pk forgery carrier) : entry.2 = carrier := by
  classical
  rw [claimsOf] at hentry
  split at hentry
  · obtain ⟨input, -, hinput⟩ := List.mem_map.mp hentry
    rw [← hinput]
  · exact absurd hentry (by simp)

open scoped Classical in
/-- **And there are at most `259` of them.** -/
theorem length_claimsOf [HasQuery HashSpec Id] (publicSeed : Digest)
    (pk : PublicKey) (forgery : Forgery)
    (carrier : HandlerCarrier.State) :
    (claimsOf publicSeed pk forgery carrier).length ≤ 259 := by
  classical
  rw [claimsOf]
  split
  · rw [List.length_map, ClaimedProbes.length_claimedCandidatesOf]
  · simp

open scoped Classical in
/-- **A claim of the forgery's is an entry of the list**, which is the direction the event
implication needs. -/
theorem mem_claimsOf [HasQuery HashSpec Id] (publicSeed : Digest)
    (pk : PublicKey) (forgery : Forgery)
    (carrier : HandlerCarrier.State) (message : Bytes) (parsed : Signature)
    (hframe : forgery.message.frame = some message)
    (hparsed : Signature.fromBytes? forgery.signature = some parsed)
    (candidate : Bytes)
    (hcandidate : candidate ∈
      ClaimedProbes.claimedCandidatesOf publicSeed carrier.cache pk message parsed) :
    (candidate, carrier) ∈ claimsOf publicSeed pk forgery carrier := by
  classical
  rw [claimsOf, hframe, hparsed]
  exact List.mem_map.mpr ⟨candidate, hcandidate, rfl⟩

/-! ## The one property the whole half rests on, at the notion that now carries it

Everything above turns on availability being **closed under the structure**: a node all of whose
children are available has an available cell. It is what stops a run from reaching a protected
cell, what makes the stalled run blind, and what answers the objection below. The disclosure
notion it is read at has changed once already — it is now the served log's — so the closure is
discharged here, at that notion, rather than left to an instantiation to notice.

Nothing had to be proved for it: `available_of_children_available` takes the
disclosed set as a **parameter**, so it holds for any, the served log's included. That is the
same lesson as the writer and the carrier — a lemma stated against what it actually uses
survives the thing it was written for changing. -/

/-- **Availability is closed under the structure at the served notion.** -/
theorem closed_disclosedByLog [HasQuery HashSpec Id] (secretSeed publicSeed : Digest)
    (pk : PublicKey) (state : (Outcome × Nat) × QueryCache HashSpec)
    (parent : StructuralNode)
    (hchildren : ∀ child ∈ parent.children,
      Available (GraphStakes.honestRevealed secretSeed publicSeed)
        (ServedLog.disclosedByLog pk state) child) :
    Available (GraphStakes.honestRevealed secretSeed publicSeed)
      (ServedLog.disclosedByLog pk state) (.structural parent) :=
  available_of_children_available _ _ hchildren

/-! ## Why the claims charge stands alone, and the run that looks like it breaks it

**The objection, which is worth stating because it will be re-proposed.** An adversary queries
the canonical input of an unavailable node, reads the cell off the answer, claims it, and
`InputBad` holds with probability one — so no constant bound on it can be right.

**It cannot do that, and the reason is in the charge's first hypothesis.** A node's canonical
input *contains its children's cells as its payload*:
`canonicalInput publicSeed cells parent = tweakableInput publicSeed parent.address
(childBytes cells parent.children)`. So forming that input already requires holding the children's
cells. And if the node's own cell is unavailable then some child's is too — that is the
contrapositive of `hclosed`, the closure hypothesis every charge here takes — so forming it
requires an unavailable cell. The recursion bottoms out at the secret seed, which no signature
discloses. "Query it and read the cell off" presupposes the cell it was supposed to produce.

What the adversary can do instead is **guess**: write `tweakableInput publicSeed addr payload`
with a payload it hopes is the cell. The handler serves a canonical answer only where
`OpenCache.openCache publicSeed (availableAt state) table` has one, which by `hclosed` is only
where every child is available — so at an unavailable node it draws fresh and the run learns
nothing. A lucky guess lower down cannot cascade upward either, for the same reason: serving the
node above needs the node below available.

**So the claims charge is sound on its own and `hclosed` is what makes it so.** The probes' own
weight pays for a different event — that some *probe* of the run is sensitive — and
`RoutedSplit.InputBad` does not quantify over the run's probes at all. -/

/-! ## The shape this half owes the join

Pinned by elaboration rather than by eye, because a mismatch between what an owner proves and
what the join takes is the failure that has cost this development most.

**The per-walk adapter is not available to this half**, and for the reason the obligation was
moved to the paired run in the first place: conditioning on the walk fixes the cell table, and
an adversary chosen knowing it makes the input event certain at that walk. So what this half
owes is `prob_sharedBad_le_expected`'s `hinput` itself, at the recorded **paired** run, with the
count the record's aiming part. `SharedJoin.hinput_of_probesIn` is for an owner whose charge is
per-walk; the ordering defect is such an owner and this one is not. -/

/-- The input half's bullet at the recorded pair.

**The target has moved one pair along and this statement is kept only as its hinge.** The
ordering defect is not a predicate of the recorded pair, so the bullet that quantifies over it
is read at the split pair: `SharedAssembly.InputBullet` is that statement, and it is what this
half now has to produce. `SharedAssembly.inputBullet_of_recorded` proves that the move costs
nothing for an ordering event that *is* a recorded-pair predicate — this statement gives that
one by transport alone — so the two are one obligation and the larger pair is the one to prove
it at.

What makes the transport free on this half's side is that `¬ ordering` is never read: the bound
below is proved for the event **without** that conjunct, which is strictly larger, so the bullet
follows by `probEvent_mono` and the ordering term is used pointwise or not at all. -/
def InputBullet (adversary : Adversary) (ordering : SharedJoin.RecordedPair → Prop) : Prop :=
  Pr[fun pair : SharedJoin.RecordedPair => Target.GoodWalk pair.1 ∧
      RoutedSplit.InputBad (SharedJoin.recordedTraceOf pair) ∧ ¬ ordering pair |
    RandomiserRecord.recordedPairedRun adversary] ≤
    (ClassExpectation.expected (RandomiserRecord.recordedPairedRun adversary)
        (fun pair => Multiset.card (SharedJoin.recordAiming pair)) + ((259 : Nat) : ℝ≥0∞)) /
      ((2 ^ 128 : Nat) : ℝ≥0∞)

end SlhDsaSecurity.ProbeContainment
