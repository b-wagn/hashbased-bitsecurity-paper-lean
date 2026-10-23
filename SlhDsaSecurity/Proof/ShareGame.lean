import SlhDsaSecurity.Proof.ShareSigner
import SlhDsaSecurity.Proof.CapComp
import SlhDsaSecurity.Proof.ClaimedProbes
import SlhDsaSecurity.Proof.OpenCache
import SlhDsaSecurity.Proof.KeygenValue

/-!
# The shared half's two games

One computation, two handlers. The computation `shareComp` is the adversary's phase — capped —
with each signing request split into a **draw** (the randomiser and the digest) and an
**assemble** (the signature, read off the table), then verification, then one **claims** query
that probes the forgery's claimed cells.

The two handlers differ in exactly two places:

* the **lenient** handler (`lenient = true`) is the real game in another representation: a
  canonical input is answered from the walk's full table, and a `PRF_msg` input at the real seed
  from the signer's own table of answers;
* the **blind** handler (`lenient = false`) answers a canonical input from the table only at an
  *open* node — all its children available — and everything else, `PRF_msg` inputs included,
  from the plain oracle.

Both raise the same sticky flag `bad` at the same steps: a recorded probe that is sensitive (a
canonical input with an unavailable child, carrying the right cell), a recorded probe in the
`PRF_msg` class at the real seed, a drawn randomiser equal to the seed, and a bad walk. Off the
flag the two handlers step identically, so the flag has the same law in both
(`ShareUntilBad`); in the blind game the flag is a union of guesses at secrets the run never
reads (`ShareBlind`).
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.ShareGame

open Security CanonicalGraph

/-! ## The fixed data -/

/-- **What the game is played at**: the two seeds the table does not carry, and the table. -/
structure Setup where
  prf : Digest
  publicSeed : Digest
  table : Cells × Padding

namespace Setup

/-- The secret seed, the table's own cell. -/
def secretSeed (setup : Setup) : Digest := setup.table.1 Node.secretSeed

/-- The walk's warm cache: every canonical input, answered in full. -/
noncomputable def warm (setup : Setup) : QueryCache HashSpec :=
  Programming.cacheFrom setup.publicSeed setup.table.1 (fullOutput setup.table.1 setup.table.2)
    Programming.order ∅

/-- The public key. -/
def pk (setup : Setup) : PublicKey :=
  { seed := setup.publicSeed, root := setup.table.1 (.structural topRoot) }

/-- The secret key. -/
def sk (setup : Setup) : SecretKey :=
  { seed := setup.secretSeed, prf := setup.prf, publicKey := setup.pk }

/-- **The walk is good**: the seeds differ and the public key is no coincidence. -/
def Good (setup : Setup) : Prop :=
  setup.prf ≠ setup.publicSeed ∧ ¬ HashSeparation.Possible (setup.publicSeed, setup.pk.root)

end Setup

/-! ## The state -/

/-- **The handler's state.** -/
structure St where
  /-- The oracle's entries outside the table. -/
  cache : QueryCache HashSpec
  /-- The signer's `PRF_msg` answers, keyed by frame. -/
  prfs : Bytes → Option HashOutput
  /-- The digests the signer has drawn, in order. -/
  served : List HashOutput
  /-- The recorded probes, each with the digests served when it was made. -/
  record : List (Bytes × List HashOutput)
  /-- The signing log. -/
  log : SigningLog

/-- The state a run starts from. -/
def St.start : St :=
  { cache := ∅, prfs := fun _ => none, served := [], record := [], log := [] }

/-! ## Availability -/

open scoped Classical in
/-- **The FORS positions the drawn digests disclose.** -/
noncomputable def disclosed (served : List HashOutput) (key : ForsKey) :
    Finset (Fin (forsTrees * 2 ^ forsHeight)) :=
  Finset.univ.filter fun index => ∃ digest ∈ served,
    SplitCharged.forsKeyOfDigest digest = key ∧
      ∃ tree : Fin forsTrees,
        GraphStakes.forsIndex (MessageDigest.forsIndices digest) tree = index

/-- **The cells available once these digests are served.** -/
noncomputable def available (setup : Setup) (served : List HashOutput) : Node → Prop :=
  Available (@GraphStakes.honestRevealed (CacheReplay.replayQuery setup.warm)
    setup.secretSeed setup.publicSeed) (disclosed served)

/-- **A sensitive probe**: the canonical input of a node with an unavailable child, carrying
that child's true cell. -/
def Sens (setup : Setup) (served : List HashOutput) (probe : Bytes) : Prop :=
  SensitiveQuery.Sensitive (GraphStakes.stakes setup.publicSeed)
    (fun served index => ¬ available setup served index) setup.table.1 served probe

/-- **The probe's verdict**: sensitive, or in the `PRF_msg` class at the real seed. -/
def Guess (setup : Setup) (served : List HashOutput) (probe : Bytes) : Prop :=
  Sens setup served probe ∨ RandomizerGate.PrfClass setup.prf probe

/-- **The entries a run may legitimately read**: the table's canonical answers at open nodes. -/
noncomputable def openAt (setup : Setup) (served : List HashOutput) : QueryCache HashSpec :=
  OpenCache.openCache setup.publicSeed (available setup served) setup.table

/-- The cache the claims are read off: the oracle's entries, and the open table. -/
noncomputable def visible (setup : Setup) (state : St) : QueryCache HashSpec := fun input =>
  match state.cache input with
  | some value => some value
  | none => openAt setup state.served input

/-! ## Answering a hash query -/

/-- The frame a `PRF_msg` input at the public seed carries. -/
def prfFrame (input : Bytes) : Bytes := input.drop (2 * n)

/-- An input is the signer's `PRF_msg` input at its own frame. -/
def IsPrfInput (setup : Setup) (input : Bytes) : Prop :=
  input = Hashing.randomizerInput setup.prf setup.publicSeed (prfFrame input)

/-- The plain oracle on the state's cache. -/
noncomputable def plain (state : St) (input : Bytes) : ProbComp (HashOutput × St) :=
  match state.cache input with
  | some value => pure (value, state)
  | none => do
      let value ← ($ᵗ HashOutput : ProbComp HashOutput)
      pure (value, { state with cache := state.cache.cacheQuery input value })

/-- The signer's `PRF_msg` answer at a frame, drawn the first time it is asked. -/
noncomputable def prfAt (state : St) (frame : Bytes) : ProbComp (HashOutput × St) :=
  match state.prfs frame with
  | some value => pure (value, state)
  | none => do
      let value ← ($ᵗ HashOutput : ProbComp HashOutput)
      pure (value, { state with prfs := Function.update state.prfs frame (some value) })

open scoped Classical in
/-- **A hash query, routed.** The lenient handler answers every canonical input from the full
table and the signer's `PRF_msg` inputs from its table; the blind one answers only open nodes
from the table and everything else from the plain oracle. -/
noncomputable def route (lenient : Bool) (setup : Setup) (state : St) (input : Bytes) :
    ProbComp (HashOutput × St) :=
  match (if lenient then setup.warm else openAt setup state.served) input with
  | some value => pure (value, state)
  | none =>
      if lenient ∧ IsPrfInput setup input then prfAt state (prfFrame input)
      else plain state input

/-! ## The computation -/

/-- A signing request's draw: its randomiser and digest. -/
abbrev DrawSpec : OracleSpec Message := Message →ₒ Option (Digest × HashOutput)

/-- A signing request's assembly. -/
abbrev AssembleSpec : OracleSpec (Message × Option (Digest × HashOutput)) :=
  (Message × Option (Digest × HashOutput)) →ₒ Option Bytes

/-- The forgery's claims. -/
abbrev ClaimSpec : OracleSpec Forgery := Forgery →ₒ Unit

/-- **The game's oracles.** -/
abbrev ShareSpec := OracleWorld + DrawSpec + AssembleSpec + ClaimSpec

/-- A world query. -/
def worldQuery (queried : OracleWorld.Domain) : ShareSpec.Domain :=
  Sum.inl (Sum.inl (Sum.inl queried))

/-- **A signing request, split.** -/
noncomputable def splitter : QueryImpl (OracleWorld + SigningSpec) (OracleComp ShareSpec) :=
  fun queried => match queried with
    | Sum.inl world => (query (spec := ShareSpec) (worldQuery world) :
        OracleComp ShareSpec (OracleWorld.Range world))
    | Sum.inr request => do
        let drawn ← (query (spec := ShareSpec) (Sum.inl (Sum.inl (Sum.inr request))) :
          OracleComp ShareSpec (Option (Digest × HashOutput)))
        (query (spec := ShareSpec) (Sum.inl (Sum.inr (request, drawn))) :
          OracleComp ShareSpec (Option Bytes))

/-- The weight the cap counts: one per hash call, one per framed signing request. -/
def weight : (OracleWorld + SigningSpec).Domain → Nat
  | Sum.inl (Sum.inl _) => 0
  | Sum.inl (Sum.inr _) => 1
  | Sum.inr request => if request.frame.isSome then 1 else 0

/-- The forgery a capped adversary gives up with. -/
def fallbackForgery : Forgery := { message := { context := [], message := [] }, signature := [] }

/-- The verifier, as world queries of the game. -/
noncomputable def verifyShare (pk : PublicKey) (forgery : Forgery) : OracleComp ShareSpec Bool :=
  simulateQ (fun world => (query (spec := ShareSpec) (worldQuery world) :
      OracleComp ShareSpec (OracleWorld.Range world)))
    (Scheme.verify (m := OracleComp OracleWorld) pk forgery.message forgery.signature)

/-- **The computation both games run.** -/
noncomputable def shareComp (adversary : Adversary) (limit : Nat) (pk : PublicKey) :
    OracleComp ShareSpec (Forgery × Bool) := do
  let forgery ← simulateQ splitter
    (CapComp.capComp weight fallbackForgery limit (adversary.main pk))
  let verified ← verifyShare pk forgery
  let _ ← (query (spec := ShareSpec) (Sum.inr forgery) : OracleComp ShareSpec Unit)
  pure (forgery, verified)

/-! ## The handlers -/

/-- **The forgery's claimed candidates**, read off the visible cache. -/
noncomputable def claimsOf (setup : Setup) (state : St) (forgery : Forgery) : List Bytes :=
  match forgery.message.frame, Signature.fromBytes? forgery.signature with
  | some message, some parsed =>
      @ClaimedProbes.claimedCandidatesOf (CacheReplay.replayQuery (visible setup state))
        setup.publicSeed (visible setup state) setup.pk message parsed
  | _, _ => []

open scoped Classical in
/-- **The handler**, lenient or blind, with the sticky flag beside its state. -/
noncomputable def handler (lenient : Bool) (setup : Setup) :
    QueryImpl ShareSpec (StateT (St × Bool) ProbComp) :=
  fun queried state => match queried with
    | Sum.inl (Sum.inl (Sum.inl (Sum.inl coin))) => do
        let value ← ($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _)
        pure (value, state)
    | Sum.inl (Sum.inl (Sum.inl (Sum.inr input))) => do
        let step ← route lenient setup state.1 input
        pure (step.1, ({ step.2 with record := state.1.record ++ [(input, state.1.served)] },
          state.2 || decide (¬ setup.Good ∨ Guess setup state.1.served input)))
    | Sum.inl (Sum.inl (Sum.inr request)) =>
        match request.frame with
        | none => pure (none, state)
        | some framed => do
            let seed ← prfAt state.1 framed
            let randomizer := Hashing.truncate seed.1
            let digest ← route lenient setup seed.2
              (Hashing.messageInput randomizer setup.pk framed)
            pure (some (randomizer, digest.1),
              ({ digest.2 with served := digest.2.served ++ [digest.1] },
                state.2 || decide (¬ setup.Good ∨ randomizer = setup.prf)))
    | Sum.inl (Sum.inr (request, drawn)) =>
        match drawn with
        | none => pure (none, ({ state.1 with log := state.1.log ++ [⟨request, none⟩] }, state.2))
        | some (randomizer, digest) =>
            let bytes := (ShareSigner.cellSig setup.warm setup.sk randomizer digest).toBytes
            pure (some bytes,
              ({ state.1 with log := state.1.log ++ [⟨request, some bytes⟩] }, state.2))
    | Sum.inr forgery =>
        let candidates := claimsOf setup state.1 forgery
        pure ((), ({ state.1 with
          record := state.1.record ++ candidates.map fun candidate => (candidate, state.1.served) },
          state.2 || decide (¬ setup.Good ∨
            ∃ candidate ∈ candidates, Guess setup state.1.served candidate)))

end SlhDsaSecurity.ShareGame
