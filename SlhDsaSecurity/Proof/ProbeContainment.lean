import SlhDsaSecurity.Proof.RedrawCell
import SlhDsaSecurity.Proof.SignerRandomiser

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

open OracleComp OracleSpec

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
    (availableAt : QueryCache HashSpec → Node → Prop) (table : Cells × Padding)
    (input : Bytes) (state : OpenCache.HandlerState)
    (z : OracleWorld.Range (Sum.inr input) × OpenCache.HandlerState)
    (hz : z ∈ support (((OpenCache.lazyProgram publicSeed availableAt table)
      (Sum.inr input)).run state)) : z.2.1 input = some z.1 := by
  classical
  have hbind : z ∈ support
      ((match state.1 input with
        | some cached => (pure (cached, state.1) : ProbComp _)
        | none =>
          match OpenCache.openCache publicSeed (availableAt state.1) table input with
          | some answer => pure (answer, state.1.cacheQuery input answer)
          | none =>
            (fun answer => (answer, state.1.cacheQuery input answer)) <$>
              ($ᵗ HashOutput : ProbComp HashOutput)) >>= fun step =>
        (pure (step.1, (step.2, state.2.1 ++ [(input, state.1)], state.2.2 + 1)) :
          ProbComp _)) := hz
  rw [mem_support_bind_iff] at hbind
  obtain ⟨step, hstep, hpure⟩ := hbind
  rw [support_pure, Set.mem_singleton_iff] at hpure
  rw [show z.1 = step.1 from by rw [hpure], show z.2.1 = step.2 from by rw [hpure]]
  cases hcached : state.1 input with
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
    (availableAt : QueryCache HashSpec → Node → Prop) (table : Cells × Padding)
    (warm : QueryCache HashSpec) (computation : OracleComp HashSpec α) :
    ∀ (state : OpenCache.HandlerState) (z : α × OpenCache.HandlerState),
      z ∈ support ((simulateQ (OpenCache.lazyProgram publicSeed availableAt table)
        (OracleComp.liftComp (simulateQ (StripCached.stripImpl warm) computation)
          OracleWorld)).run state) →
      ∀ later : QueryCache HashSpec,
        (∀ (input : Bytes) (value : HashOutput), warm input = some value →
          later input = some value) →
        (∀ (input : Bytes) (value : HashOutput), z.2.1 input = some value →
          later input = some value) →
        ∃ added : List (Bytes × QueryCache HashSpec),
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
      have hcached : step.2.1 input = some step.1 :=
        lazyProgram_hash_cached publicSeed availableAt table input state step hstepRun
      have hpersists : CacheAvailability.Persists step.2.1 z.2.1 :=
        CacheAvailability.lazyProgram_run_persists publicSeed availableAt table _ step.2 z hrest
      have hreplay : replay later input = step.1 := by
        simp [replay, hfinal input step.1 (hpersists input step.1 hcached)]
      obtain ⟨added, hadded, hprobes⟩ := ih step.1 step.2 z hrest later hwarm hfinal
      refine ⟨(input, state.1) :: added, by rw [hadded, hrecord, List.append_assoc]; rfl, ?_⟩
      intro entry hentry
      rw [hcold]
      rcases List.mem_cons.mp hentry with hhead | htail
      · rw [hhead]
        exact QueriesUnder.head _ _
      · exact QueriesUnder.tail input entry.1 _ (by rw [hreplay]; exact hprobes entry htail)

end SlhDsaSecurity.ProbeContainment
