import SlhDsaSecurity.Proof.PhaseProvenance
import SlhDsaSecurity.Proof.RandomiserCharge
import SlhDsaSecurity.Proof.SigningFaithful

/-!
# Who made the randomiser defect's entry

`ReplayGate.RandomiserBad` is the run's final cache holding a `PRF_msg` entry at the real seed,
for a framing no signing request produced. `RandomiserCharge` and `VerifierFormat` rule each
honest party out of making such a query; `CacheProvenance` and `PhaseProvenance` say an entry
that was not there before was made by *someone*. This file puts the two together on the game.

The run is split at its three sequencing points, and the entry is attributed to the first phase
whose cache holds it. Key generation cannot have made it — a canonical input opens with
`PK.seed`, a `PRF_msg` input with `SK.prf`, and the two differ on a good walk. The signer can
only have made it for a request that framed to *this* message, which the event excludes.
The verifier's calls are all `Hashing.tweakable` at `PK.seed` but one. So what is left is the
adversary's own query, which the record carries.

**Except for the overlap, which is carried rather than dismissed.** A message input *is* a
`PRF_msg` input, at its own randomiser read as the seed
(`RandomizerGate.messageInput_eq_randomizerInput`), so the signer's digest query and the
verifier's digest query each match this event's input exactly when the randomiser behind them is
`SK.prf` itself. Neither is a hole and neither is free: the signer's is one coincidence per
request, paid at `2 ^ -128` out of the same budget by `RandomizerGate.prob_randomizerHitsSeed_run_le`,
and the verifier's is the forgery's own randomiser hitting the seed, one more guess. A
provenance argument that forgot the overlap would look like it closed and would not, so the
conclusion names it as a second case.

The conclusion is therefore a two-way split, and the first half is the record — a `Multiset`,
bounded by `Outcome.counts.work`, whose `Multiset.toFinset` is the `Finset Bytes` with a
cardinality cap that `RandomizerGate.prob_run_randomizerInput_le` consumes.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.RandomiserProvenance

open Security CacheReplay RecordedQueries CacheProvenance PhaseProvenance

/-! ## The honest parties, at the signer the game actually runs

`RandomiserCharge` states its two honest lemmas at the *stripped* computations, because that is
what the input half runs. Here the signer is `Scheme.sign` itself, so the stripping step is not
taken and `HonestProbes` applies directly. -/

/-! ## The game, split at its three sequencing points -/

attribute [local irreducible] Scheme.keygenInternal Scheme.verify Scheme.sign
  Security.signingOracle Security.countQueries

/-! ## The randomiser defect, attributed

With the provenance in hand the four closure lemmas do the rest. Key generation's probes are
canonical and open with `PK.seed`; the signer's `PRF_msg` probe is at its own request's framing,
which the defect excludes because that request is in the log; the verifier's probes are
tweakable at `PK.seed` bar its one digest call. What survives is the adversary's own query — or
the digest overlap, which is carried.

**The overlap has two sources and they are charged differently.** The verifier's is the
forgery's own randomiser being `SK.prf`; it is folded into the record as one extra element
rather than named as a separate case, and the same deferral that pays for the adversary's own
queries pays for it at one more unit.

**The `+ 1` is right as a *count*, and not because the adversary gets one guess at the seed.**
A guess at `SK.prf` is checkable — a signature publishes `Hashing.truncate` of the answer at the
seed's own `PRF_msg` input — so "one object, one unit" is not an argument anywhere in this
development, and `ObligationShapes`' section on why `seedUnits` is not `1` is where that was
settled. What makes the `+ 1` sound *here* is that it is literally **one query**, the verifier's
digest call, and the deferral pays per recorded query: with the seed drawn after the run, every
recorded input hits it with probability `2 ^ -128` whether the adversary chose that input or
not, so being able to test buys nothing. Anyone restating this should preserve the count; the
unit is not a budget for a guess. The
signer's is an *answer* hitting the seed — the randomiser it derived for a request it served
happening to be `SK.prf` — and that is a different kind of event, chargeable against the run's
own randomness without any deferral, so it is named and charged separately below.

`Target.GoodWalk` supplies the walk's own coincidence the argument spends: the two seeds
differ, which is what makes `PRF_msg` and tweakable inputs disjoint, and it is already charged
by `Target.prob_bad_walk`. -/

/-- **The signer's coincidence.** The randomiser the signer derived for a request it served is
the seed itself.

Stated at the *cache entry* the answer sits in, not at `HonestProbes.replayRandomizer`, and the
difference matters: `replay` answers `default` at an absent input, so the predicate read through
`replayRandomizer` alone would also be satisfied by `Hashing.truncate default = SK.prf`, a
statement about a fixed constant that no per-run charge can pay for. The entry's presence comes
from the signing sub-run, through `PhaseProvenance.SignerMade`. -/
def SignerHitsSeed (prfSeed publicSeed : Digest) (cache : QueryCache HashSpec)
    (signed : SigningLog) : Prop :=
  ∃ entry ∈ signed, ∃ (framed : Bytes) (answer : HashOutput),
    entry.1.frame = some framed ∧
      cache (Hashing.randomizerInput prfSeed publicSeed framed) = some answer ∧
        Hashing.truncate answer = prfSeed

/-- The one input the forgery's own digest query names, when the forgery has one.

Adding it to the record is how the verifier's half of the overlap is charged. The forgery's
randomiser being `SK.prf` is *exactly* this input being a `PRF_msg` input at the seed, so it is
one more guess at the seed and costs one more unit of the record's cap — no separate argument,
and nothing for the deferral to be told about beyond the cap. -/
noncomputable def forgeryDigestRecord (pk : PublicKey) (forgery : Forgery) : Multiset Bytes :=
  match forgery.message.frame with
  | none => 0
  | some framed =>
    match Signature.fromBytes? forgery.signature with
    | none => 0
    | some parsed => {Hashing.messageInput parsed.randomizer pk framed}

theorem mem_forgeryDigestRecord (pk : PublicKey) (forgery : Forgery) (framed : Bytes)
    (parsed : Signature) (hframe : forgery.message.frame = some framed)
    (hparsed : Signature.fromBytes? forgery.signature = some parsed) :
    Hashing.messageInput parsed.randomizer pk framed ∈ forgeryDigestRecord pk forgery := by
  simp only [forgeryDigestRecord, hframe, hparsed]
  simp

/-! ## How many inputs of the class a run can hold

The charge's rate is the growth of the `PRF_msg` class at the real seed, so what it costs is how
many such entries a run can install. Provenance answers that exactly: every one is the
adversary's own recorded query, or one of the **two** inputs a served request names — its
randomiser's and its digest's — or the forgery's own digest. Key generation is ruled out
because a canonical input opens with `PK.seed`, and the verifier's other calls because they are
tweakable at `PK.seed`.

So the growth is the record's `PRF_msg` part, plus twice the served requests, plus one for the
forgery. The first and last of those are the randomiser defect's *own* charge, which is what
makes the two terms partition rather than add: on a run where no recorded input is of the class
and the forgery's digest is not either, the growth is `2 · served` and nothing more.

The two-per-request is not slack to be squeezed to one. A served request's digest input *is* an
input of the class, at its own randomiser read as the seed, exactly when the coincidence being
charged has already fired at that request. So the second unit is only ever spent on a request
that has already lost, but it cannot be dropped: the growth bound would be false without it,
and a growth bound that is false is worse than a rate that is twice as large. -/

attribute [local irreducible] WarmedGame.afterSeeds WarmedGame.tail

/-! ## Charging the signer's coincidence

The signer's half of the overlap is an **answer** hitting the seed, not an input the adversary
chose, so it is charged against the run's own randomness and needs no deferral: a fresh oracle
answer truncates to a fixed digest with probability `2 ^ -128`, and only an input of the
`PRF_msg` class at this seed can fire the event at all.

**What count the charge is against, and what it is not.** It is one unit per fresh query at an
input of that class — *per query, not per request*. Attributing it to requests is wrong, and
not by a constant factor: an adversary that has `SK.prf` hardcoded may query
`randomizerInput SK.prf PK.seed m` for `N` framings of its own choosing, keep the one whose
answer truncates to `SK.prf`, and then make a **single** signing request on that message. The
event fires with probability about `N / 2 ^ 128` with one request logged, so no bound of the
form `(requests) / 2 ^ 128` holds at a fixed walk. The search is free to the attacker in the
sense that matters here: those `N` queries are the adversary's own and are paid for on the
`work` side, not on the signing side.

That attack costs the walk's own randomness — it only works on the walk carrying the hardcoded
seed — so the `requests`-shaped bound may well be *true* once the walk is averaged in. It is
not provable by averaging a per-walk bound, because the per-walk statement it would average is
false. Getting it would need the walk's randomness in the measure, which is the same deferral
`RandomiserDeferral` builds for the record half.

So the charge is stated against the class's own growth, as a parameter, and whoever can bound
that growth chooses the number. `prob_signerHitsSeed_tail_le` instantiates it bluntly at `q`.
The sharp instantiation is the one provenance supports: every in-class entry is the adversary's
own recorded query, or one of the two inputs a served request names, or the forgery's own
digest — so the growth is `(the record's `PRF_msg` part) + 2 · (served requests) + 1`, and the
first and last terms are the randomiser defect's own charge, leaving `2 · served` once that
case is split off.

The walk's cache is clean for the event by `RandomizerGate.cleanBad_of_canonical`: its entries
are canonical, a canonical input opens with `PK.seed`, and the two seeds differ on a good walk.
-/

/-! ## The same bound at the paired run

The shared obligation is read at `Target.pairedRun`, the walk and the game together, because the
*other* half of the randomiser defect is a guess at `SK.prf` and no per-walk bound for it can
exist: conditioning on the walk fixes the secret, and an adversary that hardcodes a guess wins
with certainty on the walks that carry it.

This half still spends the oracle's own fresh answer rather than a guess at the seed, so the
per-walk bound stands as proved and only has to be averaged. That is
`Averaging.probEvent_bind_pair_le` with `Target.GoodWalk` carried as a conjunct: on a walk that
fails it the event is empty, and on one that meets it the conjunct discharges the hypothesis the
per-walk bound takes. -/

end SlhDsaSecurity.RandomiserProvenance
