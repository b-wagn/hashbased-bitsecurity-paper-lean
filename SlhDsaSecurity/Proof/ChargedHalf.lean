import SlhDsaSecurity.Proof.ServingTable
import SlhDsaSecurity.Proof.CarrierAvailability
import SlhDsaSecurity.Proof.CountedHandler

/-!
# The charge, composed at the half's own run

Everything the charge asks for is now in hand, and this file hands it over. What is charged is
`TouchedKeys.honestLinked` — the honest game at a drawn table, keys handed in, one computation —
answered by the handler that files, at the availability the carrier's served set determines.

**The one thing the chain did not already supply is the seed, and how it is supplied matters.**
The charge reads its reveal count off the run's value, by `revealedOf`, because the event is
evaluated outside the table draw. `honestLinked`'s value does not carry the drawn seed, so the
computation is wrapped. The obvious wrapper carries the reveal *function* — and it is wrong:
`hreadsRevealed` becomes immediate, but `hrevealedOf` is **unconditional**, the carried component
is an arbitrary function of its type off the support, and nothing bounds it there.

`seededLinked` carries the **seed cell** instead. Then `hrevealedOf` is
`GraphStakes.honestRevealed_le` at the carried seed, which holds at *every* seed and so holds
unconditionally, and `hreadsRevealed` is `support_map`. The rule the two wrappers teach is worth
more than either: **carry the thing the unconditional hypothesis is about, not the thing the
conditional one is about.** A wrapper that makes a support-conditioned hypothesis trivial can
make an unconditional one unprovable, and which way round it goes is not visible until both are
written.

The wrapper inherits its own blindness: two tables agreeing on `RedrawCell.seedAndRoot` agree at
the secret seed, so they carry the same seed, and `TouchedKeys.touched_honestLinked` does the
rest. That is the same pair of cells paying for a fourth thing.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.ChargedHalf

open Security CanonicalGraph OpenCache ServingProgram HandlerFacts
open WalkTable TableTail ServingTable

/-! ## The run, carrying the seed it was drawn at -/

/-- The honest linked run's value, with the drawn table's secret seed beside it. -/
abbrev SeededValue : Type :=
  ((((Forgery × Multiplicative RecordedQueries.Tally) ×
    (Bool × RecordedQueries.Tally)) × SigningLog)) × Digest × Digest

/-- **The honest linked run, carrying the two cells the charge reads off the table**: the
secret seed its availability is at, and the honest root its public key carries. Both are in
`RedrawCell.seedAndRoot`, so carrying them costs the run nothing it had not already spent. -/
noncomputable def seededLinked (adversary : Adversary) (prfSeed publicSeed : Digest)
    (table : Cells × Padding) : OracleComp OracleWorld SeededValue :=
  (fun value => (value, table.1 Node.secretSeed, table.1 (.structural topRoot))) <$>
    TouchedKeys.honestLinked adversary prfSeed publicSeed table

/-- **The carried cells are the table's.** -/
theorem cells_of_mem_support (adversary : Adversary) (prfSeed publicSeed : Digest)
    (table : Cells × Padding) (value : SeededValue)
    (hvalue : value ∈ support (seededLinked adversary prfSeed publicSeed table)) :
    value.2 = (table.1 Node.secretSeed, table.1 (.structural topRoot)) := by
  rw [seededLinked, support_map] at hvalue
  obtain ⟨inner, -, hpair⟩ := hvalue
  rw [← hpair]

/-- **The carried seed is the table's.** -/
theorem seed_of_mem_support (adversary : Adversary) (prfSeed publicSeed : Digest)
    (table : Cells × Padding) (value : SeededValue)
    (hvalue : value ∈ support (seededLinked adversary prfSeed publicSeed table)) :
    value.2.1 = table.1 Node.secretSeed :=
  congrArg Prod.fst (cells_of_mem_support adversary prfSeed publicSeed table value hvalue)

/-- **The wrapper is blind off the seed and the root too.** The run was, by
`TouchedKeys.touched_honestLinked`; what is carried beside it is the seed cell, and two tables
agreeing on `RedrawCell.seedAndRoot` agree at that. -/
theorem touched_seededLinked (adversary : Adversary) (prfSeed publicSeed : Digest)
    (left right : Cells × Padding)
    (hagree : ∀ node, RedrawCell.seedAndRoot node → left.1 node = right.1 node) :
    seededLinked adversary prfSeed publicSeed left =
      seededLinked adversary prfSeed publicSeed right := by
  rw [seededLinked, seededLinked,
    TouchedKeys.touched_honestLinked adversary prfSeed publicSeed left right hagree,
    hagree Node.secretSeed (Or.inl rfl), hagree (.structural topRoot) (Or.inr rfl)]

/-! ## The two handlers the charge compares -/

/-- The handler that files, at total availability: the lenient side. -/
noncomputable def lenientImpl (prfSeed publicSeed : Digest) (table : Cells × Padding) :
    QueryImpl OracleWorld (StateT HandlerState ProbComp) :=
  servingProgram publicSeed (keysOf prfSeed publicSeed table).2 (fun _ _ => True) table

/-- The handler that files, at the availability the carrier's served set determines. -/
noncomputable def strictImpl [HasQuery HashSpec Id] (prfSeed publicSeed : Digest)
    (table : Cells × Padding) : QueryImpl OracleWorld (StateT HandlerState ProbComp) :=
  servingProgram publicSeed (keysOf prfSeed publicSeed table).2
    (fun cache node => Available
      (GraphStakes.honestRevealed (table.1 Node.secretSeed) publicSeed)
      (ServingCarrier.disclosedAt cache) node) table

/-- **The lenient handler satisfies the facts.** At total availability the closure and the
blindness are both trivial. -/
theorem facts_lenientImpl (prfSeed publicSeed : Digest) :
    TableFacts publicSeed (fun _ _ _ => True) (fun index => ¬ RedrawCell.seedAndRoot index)
      (lenientImpl prfSeed publicSeed) :=
  tableFacts_servingProgram_keysOf prfSeed publicSeed (fun _ _ _ => True)
    (fun _ _ _ _ => trivial) (fun _ _ _ _ _ => rfl)

/-- **The strict handler satisfies them**, off the seed and the root: its key reads the root
cell and its availability reads the seed cell, and `allowed` excludes exactly those two. -/
theorem facts_strictImpl [HasQuery HashSpec Id] (prfSeed publicSeed : Digest) :
    TableFacts publicSeed
      (fun table cache node => Available
        (GraphStakes.honestRevealed (table.1 Node.secretSeed) publicSeed)
        (ServingCarrier.disclosedAt cache) node)
      (fun index => ¬ RedrawCell.seedAndRoot index) (strictImpl prfSeed publicSeed) :=
  tableFacts_servingProgram_keysOf prfSeed publicSeed
    (honestAvailableAt publicSeed ServingCarrier.disclosedAt)
    (fun _ carrier _ hchildren =>
      available_of_children_available _ (ServingCarrier.disclosedAt carrier) hchildren)
    (availBlind_honestAvailableAt publicSeed ServingCarrier.disclosedAt)

/-- **And the two are a lenient pair.** -/
theorem lenient_pair [HasQuery HashSpec Id] (prfSeed publicSeed : Digest) :
    Lenient publicSeed
      (fun table cache node => Available
        (GraphStakes.honestRevealed (table.1 Node.secretSeed) publicSeed)
        (ServingCarrier.disclosedAt cache) node)
      (lenientImpl prfSeed publicSeed) (strictImpl prfSeed publicSeed) :=
  lenient_servingProgram_keysOf prfSeed publicSeed
    (honestAvailableAt publicSeed ServingCarrier.disclosedAt)

/-! ## The charge -/

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The charge, composed.** Every hypothesis is discharged from this half's own chain: the
handlers and their facts from `ServingTable`, monotonicity from `CarrierAvailability`, blindness
from `TouchedKeys` at `RedrawCell.seedAndRoot`, availability of the root from
`RedrawCell.open_seedAndRoot`, and the reveal count off the carried seed.

What is left on the right is what the half still owes: an expected count of the probes in the
class `keep` names, and the seed-guessing avenue beside it. -/
theorem prob_charged_seededLinked [HasQuery HashSpec Id] (adversary : Adversary)
    (prfSeed publicSeed : Digest) (stall : (t : OracleWorld.Domain) → OracleWorld.Range t)
    (inner : HandlerState) (hinner : inner.2.1 = [])
    (keep : Bytes × HandlerCarrier.State → Bool)
    (hkeep : ∀ entry : Bytes × HandlerCarrier.State,
      RedrawCell.AimsSomewhere publicSeed entry.1 → keep entry = true) :
    Pr[fun pair : (SeededValue × (HandlerState × Bool)) × Cells => pair.1.2.2 = true | (do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let pad ← ($ᵗ Padding : ProbComp Padding)
        let result ← (simulateQ (HandlerLenient.sensitiveFlagged publicSeed
          (fun table cache node => Available
            (GraphStakes.honestRevealed (table.1 Node.secretSeed) publicSeed)
            (ServingCarrier.disclosedAt cache) node) (lenientImpl prfSeed publicSeed)
          (cells, pad)) (seededLinked adversary prfSeed publicSeed (cells, pad))).run
          (inner, false)
        pure (result, cells))] ≤
      (∑' z : SeededValue × (HandlerState × Bool),
          Pr[= z | (do
            let cells ← ($ᵗ Cells : ProbComp Cells)
            let pad ← ($ᵗ Padding : ProbComp Padding)
            (simulateQ (withFlag (strictImpl prfSeed publicSeed (cells, pad)))
              (seededLinked adversary prfSeed publicSeed (cells, pad))).run (inner, false))] *
            (((z.2.1.2.1.dedup.filter keep).length : Nat) : ℝ≥0∞)) /
          ((2 ^ 128 : Nat) : ℝ≥0∞) +
        Pr[fun pair : (SeededValue × (HandlerState × Bool)) × Cells =>
            ∃ entry ∈ pair.1.2.1.2.1, RedrawCell.SensitiveAtSeed (GraphStakes.stakes publicSeed)
              (fun cache node => ¬ Available
                (GraphStakes.honestRevealed pair.1.1.2.1 publicSeed)
                (ServingCarrier.disclosedAt cache) node) pair.2 entry.2 entry.1 | (do
          let cells ← ($ᵗ Cells : ProbComp Cells)
          let pad ← ($ᵗ Padding : ProbComp Padding)
          let result ← (simulateQ (withFlag (strictImpl prfSeed publicSeed (cells, pad)))
            (seededLinked adversary prfSeed publicSeed (cells, pad))).run (inner, false)
          pure (result, cells))] :=
  CarrierAvailability.prob_game_sensitive_carrier_le_canonical publicSeed
    (lenientImpl prfSeed publicSeed) (strictImpl prfSeed publicSeed)
    (facts_lenientImpl prfSeed publicSeed) (facts_strictImpl prfSeed publicSeed)
    (lenient_pair prfSeed publicSeed) stall (seededLinked adversary prfSeed publicSeed)
    RedrawCell.seedAndRoot (fun _ hnode => hnode)
    (touched_seededLinked adversary prfSeed publicSeed)
    (fun value => GraphStakes.honestRevealed value.2.1 publicSeed)
    (fun value => GraphStakes.honestRevealed_le value.2.1 publicSeed)
    (fun table value hvalue => by
      rw [seed_of_mem_support adversary prfSeed publicSeed table value hvalue])
    (fun node htouch hne value cache =>
      RedrawCell.open_seedAndRoot (GraphStakes.honestRevealed value.2.1 publicSeed)
        (GraphStakes.honestRevealed_le value.2.1 publicSeed)
        (ServingCarrier.disclosedAt cache) node htouch hne)
    inner hinner keep hkeep

/-! ## The verifier's sub-run, at the charge's own handler

`TouchedKeys.honestLinked_eq` names the verifier's term; this carries that through the two
wrappers the charge's run adds — the seed-and-root the value carries, and the flag the
comparison carries — to a membership in the support of the verifier's own sub-run, at the state
it was entered from. The verifier is the last effectful thing, so the state it leaves is the
state the whole run leaves, and that is why the statement can say `= z.2` rather than carrying
a growth. -/

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The verifier ran, and it is what left the run's final state.** -/
theorem verifier_subrun [HasQuery HashSpec Id] (adversary : Adversary)
    (prfSeed publicSeed : Digest) (table : Cells × Padding) (inner : HandlerState)
    (z : SeededValue × (HandlerState × Bool))
    (hz : z ∈ support ((simulateQ (withFlag (strictImpl prfSeed publicSeed table))
      (seededLinked adversary prfSeed publicSeed table)).run (inner, false))) :
    ∃ (mid : HandlerState × Bool)
      (verifierStep : (Bool × RecordedQueries.Tally) × (HandlerState × Bool)),
      verifierStep ∈ support ((simulateQ (withFlag (strictImpl prfSeed publicSeed table))
        (RecordedQueries.countRecorded RecordedQueries.verifierCost
          (Scheme.verify (keysOf prfSeed publicSeed table).2
            z.1.1.1.1.1.message z.1.1.1.1.1.signature))).run mid) ∧
        verifierStep.2 = z.2 := by
  classical
  rw [seededLinked, simulateQ_map, StateT.run_map, support_map] at hz
  obtain ⟨inner', hinner', hmapped⟩ := hz
  rw [TouchedKeys.honestLinked_eq, simulateQ_bind, StateT.run_bind,
    mem_support_bind_iff] at hinner'
  obtain ⟨adversaryStep, -, hrest⟩ := hinner'
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
  obtain ⟨verifierStep, hverifier, htail⟩ := hrest
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at htail
  subst hmapped
  subst htail
  exact ⟨adversaryStep.2, verifierStep, hverifier, rfl⟩

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **Every input the forgery's FORS recovery asks is one the run already drew.**

The last piece of the claims' bridge. The recovery's inputs are the verifier's, because the
verifier ran inside this computation and asked them for real;
`VerifierProbes.queriesUnder_verify_fors` is that step, and
`CountedHandler.cached_queriesUnder_counted` turns "the run asked it" into
"the carrier holds it" at the handler the charge is read under. -/
theorem cached_forsQueries [HasQuery HashSpec Id] (adversary : Adversary)
    (prfSeed publicSeed : Digest) (table : Cells × Padding) (inner : HandlerState)
    (z : SeededValue × (HandlerState × Bool))
    (hz : z ∈ support ((simulateQ (withFlag (strictImpl prfSeed publicSeed table))
      (seededLinked adversary prfSeed publicSeed table)).run (inner, false)))
    (message : Bytes) (parsed : Signature)
    (hframe : z.1.1.1.1.1.message.frame = some message)
    (hparsed : Signature.fromBytes? z.1.1.1.1.1.signature = some parsed)
    (probe : Bytes)
    (hquery : CacheReplay.QueriesUnder z.2.1.1.cache
      (SlhDsaSecurity.Fors.publicKeyFromSignature (m := OracleComp HashSpec) parsed.fors
        (MessageDigest.forsIndices (VerifierProbes.digestOf z.2.1.1.cache
          (keysOf prfSeed publicSeed table).2 message parsed))
        (keysOf prfSeed publicSeed table).2.seed
        (Scheme.forsAddress (VerifierProbes.digestOf z.2.1.1.cache
          (keysOf prfSeed publicSeed table).2 message parsed))) probe) :
    z.2.1.1.cache probe ≠ none := by
  classical
  obtain ⟨mid, verifierStep, hverifier, hstate⟩ :=
    verifier_subrun adversary prfSeed publicSeed table inner z hz
  rw [RecordedQueries.countRecorded, WarmedSplit.verify_liftM, simulateQ_map, StateT.run_map,
    support_map] at hverifier
  obtain ⟨counted, hcounted, hmapped⟩ := hverifier
  have hcarrier : counted.2.1.1 = z.2.1.1 := by rw [← hstate, ← hmapped]
  rw [← hcarrier]
  refine CountedHandler.cached_queriesUnder_counted (keysOf prfSeed publicSeed table).2
    (strictImpl prfSeed publicSeed table)
    (ServedAgreement.files_servingProgram publicSeed (keysOf prfSeed publicSeed table).2 _ table)
    RecordedQueries.verifierCost _ mid counted hcounted probe ?_
  rw [hcarrier]
  exact VerifierProbes.queriesUnder_verify_fors z.2.1.1.cache
    (keysOf prfSeed publicSeed table).2 z.1.1.1.1.1.message z.1.1.1.1.1.signature message parsed
    hframe hparsed probe hquery

/-! ## The claims, charged at the handler that will not serve them

The flag above pays for what the adversary could learn by **asking**: the difference between the
game's handler, which serves every canonical input, and the strict one, which serves only what
the signatures have disclosed. What is left is what it could get without asking, and that is the
claims' own charge — one chance per claim at a cell drawn after the run, `259` of them.

**The claims are read at the carrier's own cache, and that is not a weakening.** The forgery's
candidate list is computed by replaying the verifier, and the verifier *ran inside this
computation*: `LinkedGame.linkedAfterSeeds` contains `Scheme.verify`, and the handler caches
every answer it gives. So every input the replay asks was asked for real during the run, and its
answer is in the carrier. Nothing has to be read off the table — which is what made this
statement look impossible when the cache it was read at was the game's.

The public key comes from the run too, through the root cell the wrapper carries. -/

/-- The forgery's claimed candidates, read off the run: the carrier's cache, the carried root,
and the forgery itself. Each is paired with the carrier it is read at, which is what the charge
asks of a claim. -/
noncomputable def claimsOf [HasQuery HashSpec Id] (publicSeed : Digest)
    (z : SeededValue × (HandlerState × Bool)) : List (Bytes × HandlerCarrier.State) :=
  match (LinkedGame.outcomeOf z.1.1).1.forgery.message.frame with
  | none => []
  | some message =>
    match Signature.fromBytes? (LinkedGame.outcomeOf z.1.1).1.forgery.signature with
    | none => []
    | some parsed =>
      (ClaimedProbes.claimedCandidatesOf publicSeed z.2.1.1.cache
        ⟨publicSeed, z.1.2.2⟩ message parsed).map fun candidate => (candidate, z.2.1.1)

/-- **A claim carries the carrier it was read at.** True by construction, which is the point of
pairing them here rather than later. -/
theorem carrier_of_mem_claimsOf [HasQuery HashSpec Id] (publicSeed : Digest)
    (z : SeededValue × (HandlerState × Bool)) (entry : Bytes × HandlerCarrier.State)
    (hentry : entry ∈ claimsOf publicSeed z) : entry.2 = z.2.1.1 := by
  rw [claimsOf] at hentry
  split at hentry
  · simp at hentry
  · split at hentry
    · simp at hentry
    · obtain ⟨candidate, -, hpair⟩ := List.mem_map.mp hentry
      exact congrArg Prod.snd hpair.symm

/-- **There are at most `259` of them**, whatever the forgery is: the rejected shapes contribute
none and the served one contributes the constant `ClaimedProbes.length_claimedCandidatesOf`
names. -/
theorem length_claimsOf [HasQuery HashSpec Id] (publicSeed : Digest)
    (z : SeededValue × (HandlerState × Bool)) :
    (claimsOf publicSeed z).length ≤ 259 := by
  rw [claimsOf]
  split
  · simp
  · split
    · simp
    · rw [List.length_map, ClaimedProbes.length_claimedCandidatesOf]

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The claims cost `259 / 2 ^ 128` at the handler that will not serve them.** The second of
the half's two charges: the first pays for what asking could reveal, this one for what guessing
can. Together they are the two terms of `SharedAssembly.InputBullet`'s bound. -/
theorem prob_claimed_strict_le [HasQuery HashSpec Id] (adversary : Adversary)
    (prfSeed publicSeed : Digest) (stall : (t : OracleWorld.Domain) → OracleWorld.Range t)
    (inner : HandlerState) :
    Pr[fun pair : (SeededValue × (HandlerState × Bool)) × Cells =>
        ∃ entry ∈ claimsOf publicSeed pair.1,
          RedrawCell.SensitiveOffSeed (GraphStakes.stakes publicSeed)
            (fun cache node => ¬ Available
              (GraphStakes.honestRevealed pair.1.1.2.1 publicSeed)
              (ServingCarrier.disclosedAt cache) node) pair.2 entry.2 entry.1 | (do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let pad ← ($ᵗ Padding : ProbComp Padding)
        let result ← (simulateQ (withFlag (strictImpl prfSeed publicSeed (cells, pad)))
          (seededLinked adversary prfSeed publicSeed (cells, pad))).run (inner, false)
        pure (result, cells))] ≤
      ((259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) :=
  HandlerCharge.prob_claimed_run_le publicSeed
    (fun table cache node => Available
      (GraphStakes.honestRevealed (table.1 Node.secretSeed) publicSeed)
      (ServingCarrier.disclosedAt cache) node)
    (strictImpl prfSeed publicSeed) (facts_strictImpl prfSeed publicSeed)
    (fun table => CarrierAvailability.availableAt_mono (table.1 Node.secretSeed) publicSeed)
    (GraphStakes.stakes publicSeed) stall (seededLinked adversary prfSeed publicSeed)
    RedrawCell.seedAndRoot (fun _ hnode => hnode)
    (touched_seededLinked adversary prfSeed publicSeed)
    (fun value cache node => ¬ Available
      (GraphStakes.honestRevealed value.2.1 publicSeed)
      (ServingCarrier.disclosedAt cache) node)
    (fun value node htouch hne cache hun => hun
      (RedrawCell.open_seedAndRoot (GraphStakes.honestRevealed value.2.1 publicSeed)
        (GraphStakes.honestRevealed_le value.2.1 publicSeed)
        (ServingCarrier.disclosedAt cache) node htouch hne))
    (fun table value hvalue => by
      rw [seed_of_mem_support adversary prfSeed publicSeed table value hvalue])
    (inner, false) (claimsOf publicSeed) (carrier_of_mem_claimsOf publicSeed) 259
    (length_claimsOf publicSeed)

end SlhDsaSecurity.ChargedHalf
