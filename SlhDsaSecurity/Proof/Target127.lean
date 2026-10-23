import SlhDsaSecurity.Proof.InputBullet
import SlhDsaSecurity.Proof.CarrierTail
import SlhDsaSecurity.Proof.Target
import SlhDsaSecurity.Proof.Obligations

/-!
# The `127` socket with the ordering charge gone and the seed charge kept

`Target.target_of_obligations_fused_at` takes a `late` event that the answer half may rule out
and the shared half pays for. Every earlier instantiation took `late` to contain the **ordering
defect** — a target-recorded digest that a later signature serves — and paid for it at the
record's message-class part. That is one unit of `2 ^ -128` per message-class query, and the same
query is also a guess at `SK.prf` (its randomiser field) and a coverage target. Three units per
query against a target of two is why every ledger built on it stopped at `126`.

**The seed guess cannot be the charge that goes.** With `SK.prf` in hand an adversary computes the
digest of any message before asking for its signature, and so chooses which signatures to request
by where their FORS leaves land: covering one target's fourteen leaves at its own instance takes
about `2 ^ 78` queries, after which the forgery is certain. So a query spent finding `SK.prf` buys
a forgery, at one stake per query, and the charge on the record's `PRF_msg` candidates is real.

**The ordering defect can go.** A pre-queried digest that a later signature serves is one whose
randomiser the adversary guessed before the `PRF_msg` answer existed; that answer is a fresh draw,
so the event is thinned by `2 ^ -128` *on top of* whatever coverage it helps, and its total effect
is second order. The answer half absorbs it inside its own column — that is the answer side's
obligation below, stated with nothing excluded but the seed guess.

So this socket takes `late := PrfHit ∨ SignerHit`: some query the adversary or the verifier made
is a `PRF_msg` input at the walk's `SK.prf`, or some signature's randomiser *is* `SK.prf`. The
second is there because it is what keeps the seed hop's blind game from being blind: when the
signer's own digest query happens to be a `PRF_msg` input at the real seed, the game reads the
seed through the signer and not through the adversary.

**The shared half is one obligation, not a sum of two, and that is forced.** A guess charge in
the real order — secret drawn first — is false at the expected count of the real run: an
adversary that stops guessing once it has hit makes `Pr[hit]` exceed `E[guesses] / 2 ^ 128` by a
second-order amount, and the ledger has no slack for any amount. The count has to be taken in the
blind game, where the secret is drawn after the run. Two such charges taken in two blind games
cannot then be added inside one record: each count is bounded by the record pathwise, but only in
its own game. So the input half's aiming guesses and the `SK.prf` guesses have to be counted in
**one** game blind to both, where `aiming + candidates ≤ record` holds pathwise — which is what
`card_aiming_add_candidates_le_record` is for.

What is assumed here:

* `hanswer` — the answer half at the carrier tail, with only `late` excluded;
* `hshared` — the input half and `late`, together, against one record and the forgery's claims.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.Target127

open Security WarmedGame Target ClassExpectation SharedJoin RandomiserRecord LateProbes

/-! ## The seed guess and the record part that pays for it -/

/-- An input whose first `n` bytes are the encoding of `seed`. -/
def SeedPrefixed (seed : Digest) (input : Bytes) : Prop :=
  ∃ rest : Bytes, input = bytesBE n seed ++ rest

/-- **The seed guess.** Some query of the adversary or the verifier is a `PRF_msg` input at the
walk's `SK.prf`. -/
def PrfHit (pair : RecordedPair) : Prop :=
  RecordMeetsPrfClass pair.1.1.1.2.1 pair.2

/-- **The signer's coincidence**: some signature's randomiser is the walk's `SK.prf`. -/
def SignerHit (pair : RecordedPair) : Prop :=
  RandomiserProvenance.SignerHitsSeed pair.1.1.1.2.1 pair.1.1.1.2.2 pair.2.2 pair.2.1.1.1.signed

/-- **The defect at the recorded pair**: the seed guess or the signer's coincidence. -/
def Late (pair : RecordedPair) : Prop := PrfHit pair ∨ SignerHit pair

/-- **The defect at the split pair**, read through the recordings' forgetting. -/
def late (pair : SplitPair) : Prop := Late (forgetRecordings pair)

open scoped Classical in
/-- **The record's `PRF_msg` candidates**: its entries not prefixed by `PK.seed`. -/
noncomputable def recordPrfCandidates (pair : RecordedPair) : Multiset Bytes :=
  (recordOf pair).filter fun input => ¬ SeedPrefixed pair.1.1.1.2.2 input

/-- A `PRF_msg` input at `prf` is prefixed by `prf`. -/
theorem seedPrefixed_of_prfClass {prf : Digest} {input : Bytes}
    (hprf : RandomizerGate.PrfClass prf input) : SeedPrefixed prf input := by
  obtain ⟨seed, message, rfl⟩ := hprf
  exact ⟨bytesBE n seed ++ message, by simp [Hashing.randomizerInput, List.append_assoc]⟩

/-- Two seeds' prefixes are the same prefix only when the seeds are equal. -/
theorem eq_of_seedPrefixed {left right : Digest} {input : Bytes}
    (hleft : SeedPrefixed left input) (hright : SeedPrefixed right input) : left = right := by
  obtain ⟨leftRest, rfl⟩ := hleft
  obtain ⟨rightRest, hsame⟩ := hright
  have htake := congrArg (List.take n) hsame
  simp only [List.take_left' (length_bytesBE n left), List.take_left' (length_bytesBE n right)]
    at htake
  exact bytesBE_injective n htake

/-- **An aiming probe is prefixed by `PK.seed`**: it is a tweakable input at the public seed. -/
theorem seedPrefixed_of_aimsSomewhere {publicSeed : Digest} {input : Bytes}
    (haims : RedrawCell.AimsSomewhere publicSeed input) : SeedPrefixed publicSeed input := by
  classical
  rw [RedrawCell.AimsSomewhere, GraphStakes.locate] at haims
  split at haims
  · rename_i hsome
    obtain ⟨node, cell, rfl⟩ := hsome
    exact ⟨node.parent.address.toBytes ++ bytesBE n cell,
      by simp [GraphStakes.inputOf, Hashing.tweakableInput, List.append_assoc]⟩
  · exact absurd rfl haims

open scoped Classical in
/-- **The two shared parts fit in one record.** Aiming probes are `PK.seed`-prefixed and the
candidates are not, so they are disjoint filters of the record. -/
theorem card_aiming_add_candidates_le_record (pair : RecordedPair) :
    Multiset.card (recordAiming pair) + Multiset.card (recordPrfCandidates pair) ≤
      Multiset.card (recordOf pair) := by
  classical
  have haim : recordAiming pair ≤
      (recordOf pair).filter fun input => SeedPrefixed pair.1.1.1.2.2 input := by
    rw [recordAiming]
    exact Multiset.monotone_filter_right _ fun input haims =>
      seedPrefixed_of_aimsSomewhere haims
  have hsplit := Multiset.filter_add_not (fun input => SeedPrefixed pair.1.1.1.2.2 input)
    (recordOf pair)
  calc Multiset.card (recordAiming pair) + Multiset.card (recordPrfCandidates pair)
      ≤ Multiset.card ((recordOf pair).filter fun input => SeedPrefixed pair.1.1.1.2.2 input) +
          Multiset.card (recordPrfCandidates pair) :=
        Nat.add_le_add_right (Multiset.card_le_card haim) _
    _ = Multiset.card (recordOf pair) := by
        rw [recordPrfCandidates, ← Multiset.card_add, hsplit]

/-- **On a good walk a seed guess is a candidate.** The walk's `SK.prf` differs from its
`PK.seed`, so an input carrying the first is not prefixed by the second. -/
theorem exists_candidate_of_prfHit (pair : RecordedPair) (hgood : GoodWalk pair.1)
    (hhit : PrfHit pair) :
    ∃ input ∈ recordPrfCandidates pair, RandomizerGate.PrfClass pair.1.1.1.2.1 input := by
  classical
  obtain ⟨input, hinput, hprf⟩ := hhit
  refine ⟨input, ?_, hprf⟩
  rw [recordPrfCandidates, Multiset.mem_filter]
  refine ⟨Multiset.mem_toFinset.mp hinput, fun hseed => hgood.1 ?_⟩
  exact eq_of_seedPrefixed (seedPrefixed_of_prfClass hprf) hseed

/-! ## The target -/

end SlhDsaSecurity.Target127
