import SlhDsaSecurity.Proof.ChargedProbe
import SlhDsaSecurity.Proof.LazyBridge
import SlhDsaSecurity.Proof.AddressBounds

/-!
# A cell a run cannot read may be drawn after it

`ChargedProbe.prob_run_sensitive_le` charges a run one unit of `2 ^ -128` per probe, with the
cell it is charged against drawn *after* the run. `OpenCache.evalDist_stalled_lazyProgram_congr`
offers something weaker in form though equal in content: the run's law is unchanged by altering
that cell, a congruence rather than a factorisation.

`evalDist_redraw_coordinate` converts the one into the other. If altering one coordinate of the
cell table leaves a run's law alone, then the joint law of the run's result and that coordinate
is the same as the law of the result together with an *independently* drawn cell — the
coordinate may be redrawn. `evalDist_uniformSample_bind_update` is what makes it
short: a uniform table is a uniform table with one coordinate overwritten by a fresh uniform
value, so the overwriting value can be substituted for the coordinate everywhere and then
commuted past the run.

Only the cell is freed, not the padding of its node. That is a *stronger* hypothesis than
`OpenCache.AgreeOff`, so the congruence supplies it directly, and it keeps the statement about
the cell table alone with everything else carried along as auxiliary randomness.
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.RedrawCell

open CanonicalGraph SensitiveQuery

/-- **A coordinate a run cannot read may be redrawn.** -/
theorem evalDist_redraw_coordinate {γ Aux : Type} (index : CanonicalGraph.Node)
    (auxiliary : ProbComp Aux) (run : Cells → Aux → ProbComp γ)
    (hcongr : ∀ (cells other : Cells) (aux : Aux),
      (∀ node, node ≠ index → cells node = other node) →
        𝒟[run cells aux] = 𝒟[run other aux]) :
    𝒟[do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let aux ← auxiliary
        let result ← run cells aux
        pure (result, cells index)] =
      𝒟[do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let aux ← auxiliary
        let result ← run cells aux
        let cell ← ($ᵗ Cell : ProbComp Cell)
        pure (result, cell)] := by
  classical
  have hupdate := evalDist_uniformSample_bind_update
    (D := CanonicalGraph.Node) (R := Cell) index
  calc 𝒟[do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let aux ← auxiliary
        let result ← run cells aux
        pure (result, cells index)]
      = 𝒟[(do
            let cell ← ($ᵗ Cell : ProbComp Cell)
            let cells ← ($ᵗ Cells : ProbComp Cells)
            pure (Function.update cells index cell)) >>= fun cells => do
          let aux ← auxiliary
          let result ← run cells aux
          pure (result, cells index)] :=
        (LazyBridge.evalDist_bind_congr_right hupdate _).symm
    _ = 𝒟[do
          let cell ← ($ᵗ Cell : ProbComp Cell)
          let cells ← ($ᵗ Cells : ProbComp Cells)
          let aux ← auxiliary
          let result ← run (Function.update cells index cell) aux
          pure (result, cell)] := by
        simp only [bind_assoc, pure_bind, Function.update_self]
    _ = 𝒟[do
          let cell ← ($ᵗ Cell : ProbComp Cell)
          let cells ← ($ᵗ Cells : ProbComp Cells)
          let aux ← auxiliary
          let result ← run cells aux
          pure (result, cell)] := by
        refine OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ fun cell => ?_
        refine OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ fun cells => ?_
        refine OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ fun aux => ?_
        refine LazyBridge.evalDist_bind_congr_right ?_ _
        exact hcongr _ _ aux fun node hnode => Function.update_of_ne hnode _ _
    _ = 𝒟[do
          let cells ← ($ᵗ Cells : ProbComp Cells)
          let cell ← ($ᵗ Cell : ProbComp Cell)
          let aux ← auxiliary
          let result ← run cells aux
          pure (result, cell)] :=
        OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
    _ = 𝒟[do
          let cells ← ($ᵗ Cells : ProbComp Cells)
          let aux ← auxiliary
          let cell ← ($ᵗ Cell : ProbComp Cell)
          let result ← run cells aux
          pure (result, cell)] := by
        refine OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ fun cells => ?_
        exact OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
    _ = _ := by
        refine OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ fun cells => ?_
        refine OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ fun aux => ?_
        exact OracleComp.DeferredSampling.evalDist_bind_comm _ _ _

/-! ## The charge against the joint draw

With the coordinate redrawn, the per-cell charge applies to the run itself. Summed over the
cells it comes to one unit per probe, the weights adding to the probe count. -/

open ChargedProbe

variable {Target : Type}

/-! ## The charge against one cell, at the game's handler

The three pieces meet here. Stalling at the cell leaves the chance of a charge against it
alone; the stalled run does not read that cell, so it may be drawn after; and the weight the
drawn cell costs is the number of probes aiming at it, which stalling also leaves alone.

**`HandlerCharge` is this section and the run-level one below it at an arbitrary handler**,
against `HandlerFacts.Facts`. Note what the copies do *not* take: `hclosed` is absent there,
because closure of availability under the structure was only ever used to prove that the
stalled run does not read the cell, and `Facts.blind` is that congruence. These stay as the
instance their existing readers name. -/

open OpenCache ChargedProbe

/-! ## The two avenues, kept apart

A sensitive query stakes one cell, and which cell it is decides which charge pays for it. The
secret seed is its own avenue: a node staked on it is a `wotsPrf` or a `forsPrf`, its canonical
input is `TrackedQueries.prfInput`, and `TrackedQueries.prob_meets_real_le` charges that event
on its own. It has to be its own avenue, because the computation carries the secret seed as
*data* — it is the seed key generation is run from — and that seed is a cell of the table, so no
run is blind to it and the redrawing below cannot reach it.

Every other cell is reached, and `SensitiveOffSeed` is exactly that half of the event. The two
are complementary, which is what lets the counts be added: a query's address names its node
before any cell is read, so a probe falls in one avenue or the other and never both.

The computation is allowed to read more than the seed, and what it may read is a parameter:
`touched` names the cells it reads, and `hopen` asks that every one of them but the seed be
available at every state. Such a cell costs nothing to exclude, since no query staking it is
sensitive at any state — the event at that index is empty. A public value the computation
carries, such as the honest root, is of that kind. A cell the signatures only make available
part way through is not, and may not be put in `touched`. -/

/-! ### The honest phase aims nowhere

The weights have to be read off the *recorded* queries — the adversary's and the verifier's —
and the handler's record holds more than those: the stripped honest phase still asks for each
signature's randomiser and message digest. Those probes have to contribute nothing, and they do,
for the two reasons `Target.GoodWalk` already names and pays for. A randomiser input opens with
`SK.prf`, which is not the public seed; a message input would have to make the public key encode
a structural address, which the walk's second coincidence is exactly the absence of. Both are
`HashSeparation`'s, read here through the stakes' own `locate`. -/

/-! ## The input half's charge

Summed over the cells. Each cell's charge is weighted by the probes aiming at it, those weights
add to the number of probes, and the sum over cells meets the expectation over runs through
`ChargedProbe.sum_tsum_comm`. What is left is the four things the game supplies: closure of
availability under the structure, its monotonicity in the cache, a bound on the recorded
probes, and the stakes structure. -/

/-! ## The game's run is this one with the record forgotten

The charge is about a handler that keeps a record; a game's run has no record. At total
availability the two are the same run. The handler answers from the table at every canonical
input, and the game's cache already holds those entries — the walk programmed them there — so
the handler's table branch is never reached, and what is left is the shared oracle with a
record alongside. Forgetting the record gives the game's run back.

Nothing about the walk's distribution is used, only that its cache carries the canonical
entries. There is no order condition and no deferred sampling: the equality is step by step. -/

/-! ## The programmed cache read on demand

The run above starts from the game's cache, which already carries the cells, so the charge —
which is about a run blind to them — cannot be read off it. What the charge wants is the handler
started from nothing, drawing the programmed entries only as they are asked for.

That run is the game's run too. At total availability the handler serves exactly the entries the
walk programmed, so at every moment the game's cache is the programmed entries with whatever the
handler has drawn beside them, and the two answer every query alike. The relation between the
two caches is an equation, not a coupling: `unionCache` says what the game holds while the
handler holds its own, and one induction carries it. -/

open scoped Classical in
/-- At total availability every node is open. -/
theorem openNodes_total :
    OpenCache.openNodes (fun _ => True) = CanonicalGraph.Programming.order := by
  simp [OpenCache.openNodes]

open scoped Classical in
/-- **At total availability the readable entries are the whole programmed cache** — the one the
walk leaves behind. -/
theorem openCache_total (publicSeed : Digest) (table : Cells × Padding) :
    openCache publicSeed (fun _ => True) table =
      CanonicalGraph.Programming.cacheFrom publicSeed table.1
        (CanonicalGraph.fullOutput table.1 table.2) CanonicalGraph.Programming.order ∅ := by
  rw [openCache, openNodes_total]

/-! ## The walk's own table

`WarmedGame.mem_support_graphWalk` hands the walk's cache as a programmed table over an
arbitrary output table; the handler wants a cells-and-padding pair. `Programming.splitTable` is
the bijection between the two, and the match is a reindexing along it. The secret seed is where
a mismatch would sit, and there is none: the bijection puts it in the table's own `secretSeed`
cell and leaves it there. -/

/-- **Every cells-and-padding pair is a seed and an output table.** -/
theorem splitTable_fullOutput (table : Cells × Padding) :
    CanonicalGraph.Programming.splitTable
        (table.1 CanonicalGraph.Node.secretSeed,
          CanonicalGraph.fullOutput table.1 table.2) = table := by
  refine Prod.ext (funext fun node => ?_) (funext fun parent => ?_)
  · cases node with
    | secretSeed => rfl
    | structural parent => exact CanonicalGraph.truncate_fullOutput _ _ _
  · exact BitVec.extractLsb'_append_eq_right

/-- The programmed entries, with whatever the handler has drawn beside them. -/
noncomputable def unionCache (publicSeed : Digest) (table : Cells × Padding)
    (cache : QueryCache HashSpec) : QueryCache HashSpec :=
  fun input =>
    match openCache publicSeed (fun _ => True) table input with
    | some answer => some answer
    | none => cache input

theorem unionCache_of_open (publicSeed : Digest) (table : Cells × Padding)
    (cache : QueryCache HashSpec) (input : Bytes) (answer : HashOutput)
    (hopen : openCache publicSeed (fun _ => True) table input = some answer) :
    unionCache publicSeed table cache input = some answer := by
  rw [unionCache, hopen]

/-- **The cells the union cache computes are the table's own.** The programmed entries answer
every canonical input, so replaying the graph through this cache returns the cells it was
programmed from — whatever else the handler has drawn beside them. -/
theorem replayCells_unionCache (publicSeed : Digest) (table : Cells × Padding)
    (cache : QueryCache HashSpec) :
    HonestProbes.replayCells (unionCache publicSeed table cache)
        (table.1 CanonicalGraph.Node.secretSeed) publicSeed = table.1 := by
  have hvalue := @CanonicalGraph.Programming.value_eq_of_cache_agreement
    (CacheReplay.replayQuery (unionCache publicSeed table cache)) publicSeed
    (table.1 CanonicalGraph.Node.secretSeed)
    (CanonicalGraph.fullOutput table.1 table.2)
    (fun input output hentry => by
      refine CacheReplay.hash_replayQuery (unionCache publicSeed table cache) input output ?_
      refine unionCache_of_open publicSeed table cache input output ?_
      rw [openCache_total]
      rw [show CanonicalGraph.Programming.cellsOfOutputs (table.1 CanonicalGraph.Node.secretSeed)
          (CanonicalGraph.fullOutput table.1 table.2) = table.1 from
        congrArg Prod.fst (splitTable_fullOutput table)] at hentry
      exact hentry)
  rw [HonestProbes.replayCells, hvalue,
    show CanonicalGraph.Programming.cellsOfOutputs (table.1 CanonicalGraph.Node.secretSeed)
        (CanonicalGraph.fullOutput table.1 table.2) = table.1 from
      congrArg Prod.fst (splitTable_fullOutput table)]

/-! ## What a signature reads, as a congruence

The handler that answers signing requests does not need a cell-reading signer of its own; what
`OpenCache.reading_step_congr` consumes is `hreads`, "the step is a function of the cells it
reads", and that is a congruence. So the statements here are congruences: change the table only
away from the cells a signature discloses and the signature does not move.

Writing a separate cell-reading signer and proving it equal to the honest one would pay for the
construction twice — once to carry the hypertree's two bounds through a dependent recursion, and
once to prove the result is what the honest signer already computes. The congruence is the half
that is actually used. -/

/-- The nodes an honest FORS signature discloses: the secret at each selected leaf, and the
sibling at each level of its authentication path. -/
def ForsDiscloses (key : ForsKey) (indices : Fors.Indices) : CanonicalGraph.Node → Prop :=
  fun node =>
    (∃ tree, node = .structural (HonestProbes.forsSecretNode key indices tree)) ∨
      ∃ tree level, node = .structural (HonestProbes.forsAuthNode key indices tree level)

/-- Two FORS tree signatures agree when their fields do. -/
theorem forsTreeSignature_eq {left right : ForsTreeSignature}
    (hsecret : left.secret = right.secret)
    (hauth : left.authentication = right.authentication) : left = right := by
  cases left
  cases right
  simp_all

/-- **An honest FORS signature reads only the cells it discloses.** -/
theorem fors_sign_congr (publicSeed : Digest) (cache : QueryCache HashSpec)
    (left right : Cells × Padding) (key : ForsKey) (indices : Fors.Indices)
    (hagree : ∀ node, ForsDiscloses key indices node → left.1 node = right.1 node) :
    @Fors.sign Id _ (CacheReplay.replayQuery (unionCache publicSeed left cache)) indices
        (left.1 CanonicalGraph.Node.secretSeed) publicSeed key.address =
      @Fors.sign Id _ (CacheReplay.replayQuery (unionCache publicSeed right cache)) indices
        (right.1 CanonicalGraph.Node.secretSeed) publicSeed key.address := by
  funext tree
  refine forsTreeSignature_eq ?_ (funext fun level => ?_)
  · rw [HonestProbes.fors_sign_secret_cell, HonestProbes.fors_sign_secret_cell,
      replayCells_unionCache, replayCells_unionCache]
    exact hagree _ (Or.inl ⟨tree, rfl⟩)
  · rw [HonestProbes.fors_sign_authentication_cell, HonestProbes.fors_sign_authentication_cell,
      replayCells_unionCache, replayCells_unionCache]
    exact hagree _ (Or.inr ⟨tree, level, rfl⟩)

/-- Two XMSS signatures agree when their fields do. -/
theorem xmssSignature_eq {left right : XmssSignature} (hwots : left.wots = right.wots)
    (hauth : left.authentication = right.authentication) : left = right := by
  cases left
  cases right
  simp_all

/-! ## The signature's own two inputs

A signature is its randomiser and its digest, which no table answers, and then a FORS part and
a climb, which are cells. This settles the first two: neither input is canonical, so both
tables answer them from the same cache and they cannot differ.

Two of the hypotheses are carried rather than discharged, and are the walk's business: that the
public key is no coincidence, and that the signer's PRF seed is not the public seed. Each is a
walk defect `Target` pays for once, and paying it again here would be paying twice. The third
that the separation lemmas want, that addresses are within bounds, is *not* carried —
`withinBounds_structural` closes it. -/

/-! ## The congruences at one shared seed

A signer carries one secret key, so both sides of a congruence use the same secret seed rather
than each table's own. The two are the same value whenever the table's seed cell is the key's,
which is what the use site has, and these are the congruences in that form. -/

/-! ## The signature, as one congruence

The four parts meet here. The randomiser and the digest are answered by the cache, the FORS part
and the climb are cells, and so the whole signature is unchanged by a table agreeing at the
cells it discloses.

`hsigned` is a parameter and the debt it stands for is real. It says the leaves *this digest*
selects are signed, which is what makes their secrets available, and it is true for an
**ordering** reason: the signer queries its digest before it reads any FORS secret, so by the
time it reads one the cache already holds what makes that secret available. Instantiating this
parameter against `CacheAvailability.signedAt` means **proving that ordering, not recalling
it**. It is stated about `signedDigest left cache sk message`, the digest the signer actually
computes; the quantified version would be the much stronger claim that every leaf of every
digest is signed, which is false and would make everything available. -/

/-- The cells the union cache computes, one node at a time. -/
theorem value_unionCache (publicSeed : Digest) (table : Cells × Padding)
    (cache : QueryCache HashSpec) (node : CanonicalGraph.Node) :
    @CanonicalGraph.value (CacheReplay.replayQuery (unionCache publicSeed table cache))
        (table.1 CanonicalGraph.Node.secretSeed) publicSeed node = table.1 node :=
  congrFun (replayCells_unionCache publicSeed table cache) node

/-- Two signatures built part by part agree when the parts do. Stated over six variables on
purpose: applying it is first-order, so nothing ever asks the unifier to walk into two large
terms that differ only inside a handler instance. -/
theorem signature_mk_eq {randomizerLeft randomizerRight : Digest}
    {forsLeft forsRight : ForsSignature}
    {hypertreeLeft hypertreeRight : HypertreeSignature}
    (hrandom : randomizerLeft = randomizerRight) (hfors : forsLeft = forsRight)
    (hhypertree : hypertreeLeft = hypertreeRight) :
    Signature.mk randomizerLeft forsLeft hypertreeLeft =
      Signature.mk randomizerRight forsRight hypertreeRight := by
  rw [hrandom, hfors, hhypertree]

/-! ## The signature, as one congruence

The four parts meet here. The randomiser and the digest are answered by the cache, the FORS part
and the climb are cells, and so the whole signature is unchanged by a table agreeing at the
cells it discloses.

**Normalise the digest before anything else.** Every other part is indexed by it — the FORS
indices, the FORS address, the tree and the leaf the climb starts at — so a rewrite that fires
first and moves the digest off the shape `signedDigest_congr` speaks about leaves the digest
rewrite unable to fire, and the symptom is a pattern plainly present and not found. Rewriting
the randomiser first does exactly that: it makes one side's digest the digest of *the other
side's* randomiser.

`hsigned` is a parameter and the debt it stands for is real. It says the leaves *this digest*
selects are signed, which is what makes their secrets available, and it is true for an
**ordering** reason: the signer queries its digest before it reads any FORS secret, so by the
time it reads one the cache already holds what makes that secret available. Instantiating this
parameter against `CacheAvailability.signedAt` means **proving that ordering, not recalling
it**. It is stated about `signedDigest left cache sk message`, the digest the signer actually
computes; the quantified version would be the much stronger claim that every leaf of every
digest is signed, which is false and would make everything available. -/

/-! ## The charge, at the presentation the game gives

Everything the two halves need is in place, so they join. The flag the comparison carries is a
function of the record; the record's entries name nodes the charge's stakes already cover; and
the wrapper the charge is proved about differs from the comparison's only in what it writes to
that flag. What comes out is one bound on the game's own presentation — the handler at total
availability, which `probEvent_rom_eq_lazy` identifies with the game's run — with the record and
its limit left as parameters.

**`HandlerLenient` has `prob_game_sensitive_le` and its honest instance at an arbitrary pair of
handlers**, from two `HandlerFacts.Facts` and one `HandlerFacts.Lenient`. That is the form the
served notion needs, since only a handler that files keeps a served set for its availability to
be read from. -/

end SlhDsaSecurity.RedrawCell
