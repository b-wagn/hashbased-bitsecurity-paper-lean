import SlhDsaSecurity.Proof.RedrawCell
import SlhDsaSecurity.Proof.SignerRandomiser
import SlhDsaSecurity.Proof.SharedJoin
import SlhDsaSecurity.Proof.KeygenValue
import SlhDsaSecurity.Proof.ServedBridge
import SlhDsaSecurity.Proof.ServingCarrier
import SlhDsaSecurity.Proof.ChargedProbe

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

/-! ## What the honest phase consults, at the game's cache -/

/-! ## The honest phase's probes, at the game's cache

The game's cache is the table's entries with whatever the handler has drawn beside them, which
is `RedrawCell.unionCache`; it extends the entries stripping answers from, so `queriesUnder_strip`
applies, and the cells it replays are the table's own. So a canonical probe is one the table
answers — which stripping never forwards — and what reaches the handler is the randomiser and
the digest, neither of which aims at a cell. -/

/-! ## What the handler records while the honest phase runs

The per-probe facts above are about what a computation *consults*, read along the replay path at
a cache; the handler's record holds what a **run** forwarded. `strip_probes_queriesUnder` is the
bridge, and it is the `laterCache` pattern once more: the statement is read at any cache
extending both the table's entries and the handler's own, because that is the only cache at
which the run's answers and the replayed ones agree — the table's where the table answered, the
handler's where it drew. -/

open scoped Classical in
/-! ## What the containment reads of a handler

The count is a fact about the handler's **probe list and its cache**, and about nothing else: a
hash step appends one probe and leaves its own input cached, a coin step appends none, and a run
keeps what it cached. `ServingProgram.servingProgram` is `OpenCache.lazyProgram` with one
addition — a query the in-flight framing recognises is filed into the carrier in the same step —
and filing touches neither the list nor the cache. So the containment holds at both, and the
**second instance is what makes this an interface** rather than a generalisation written ahead of
its use: the charge the containment pays is stated at the serving handler, and the containment
was stated at the lazy one.

`HandlerFacts.Facts` does not carry this. Its fields are about the carrier and the record; the
cache is not among them, and `cached` is the field the replay argument turns on. -/

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

/-! ## Counting the aiming probes against the record's aiming part

**The half does not owe a constant here.** It does not. `InputBullet` at the end of this file pays
`expected (card recordAiming) + 259`, because a claimed cell is checkable against the
authentication path and the adversary's chances are its queries. The record's aiming part *is*
precisely the probes whose address locates a cell, which is to say precisely those tests, so
that expected count is the half's payment and this machinery is where to look first when
`InputBullet.ClaimsCharged` is proved.

The weight is a count of the handler's list; the budget pays out of the run's recorded multiset.
Both sides are counted by the same test, and a step moves them together: a hash call appends one
probe and records one input, and a probe that aims is an input that aims.

**The route now runs to the handler the charge is stated at.** Everything from here to
`weight_le_recordAim_at` was written against `OpenCache.lazyProgram`; the charge it pays is
stated against `ServingProgram.servingProgram`. The two differ by a filing step, and filing
touches neither the probe list nor the cache, which are the only two things this argument reads.
So the route is stated against `Probing` instead of against a handler, and
`weight_le_recordAim_serving` is the instance the half reaches for. -/

attribute [local irreducible] Scheme.keygenInternal Scheme.sign Scheme.verify

/-! ## The record is no larger than the probe list

The containment above compares the handler's **aiming** probes with the record's aiming part,
and it needs the honest phase stripped to do it. The unfiltered comparison points the other way
and needs nothing: every recorded query is a probe the handler saw, and a phase that records
nothing can only add probes. So the record is a sub-count of the probe list on **every** run —
no seed, no public-key separation, no stripping, and the signer may be the real one.

This is what a half paying against the probe list rather than against the record needs: the
three parts still fit in two of them, because each part is a part of the record and the record
is a part of this. -/

/-! ## What the charge may take

The weight the charge carries is the **de-duplicated** aiming part of the handler's record, and
the budget pays out of the aiming part of the run's own. The first is at most the second:
de-duplicating only shortens a list, and the count above is an identity rather than a bound, so
nothing accumulates between them. -/

/-! ## The same, with the keys handed in

The charge reads the game with key generation already replaced by the value the walk's cache
determines, because that is what lets the signer's reads of the table be frozen. The containment
is simpler there, not harder: with no key generation in the computation there is no keygen step
to account for, and the assembly is the adversary's phase and the verifier's. -/

/-! ## The export, in the join's vocabulary

**Also currently unused**, for the same reason as the counting above: the half's bullet is paid
by the claims alone, so it discharges no containment at the join. It is kept because the shape
is the one a moved split would need, and because `recordAim_eq_card_recordAiming` is what stops
this half's test and the join's from drifting apart unnoticed.

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

/-! ## The forgery's claims never stake the secret seed

The half is charged at `RedrawCell.SensitiveOffSeed`, the avenue whose staked cell is not the
secret seed; the seed's own avenue is charged elsewhere and must not be paid for twice. For the
forgery's claims the distinction costs nothing, and structurally rather than by hypothesis:
every claimed candidate is the canonical input of a FORS leaf or a WOTS chain step, whose staked
cell is a **structural** node — a signature carries no claim about the seed. So a sensitive
claim is a sensitive claim off the seed, and the seed term does not arise on this side at all.
-/

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

/-! ## The claims the charge is handed

The charge takes its list as a function of the run's result and pairs each entry with the
carrier availability is read at, so the half builds its own list rather than growing a
carrier-valued twin of `WarmProbes.claimedEntries`: the list is the half's and nobody else reads
it.

A forgery whose frame or signature does not parse claims nothing, so the list is empty there —
which is sound because `RoutedSplit.InputBad` requires both to parse before it asks anything
else. Its length is `259` when they do and `0` when they do not, so the constant bounds it
either way. -/

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

/-! ## What `hclosed` rules out, and the test it does not rule out

**The half does not owe a constant.** This section exists so that nobody re-derives that it
does, which is easy to do from `hclosed` alone and is how the earlier version of this text went
wrong. Two questions get asked at once here and they have different answers: *can the adversary
read an unavailable cell off an answer* — no, and `hclosed` is why — and *can it guess one and
find out whether it guessed right* — yes, at one query per candidate, and that is what makes the
charge `q`-shaped.

**Reading a cell off an answer is impossible, and `hclosed` is why.** A node's canonical
input *contains its children's cells as its payload*:
`canonicalInput publicSeed cells parent = tweakableInput publicSeed parent.address
(childBytes cells parent.children)`. So forming that input already requires holding the children's
cells. And if the node's own cell is unavailable then some child's is too — that is the
contrapositive of `hclosed`, the closure hypothesis every charge here takes — so forming it
requires an unavailable cell. The recursion bottoms out at the secret seed, which no signature
discloses. "Query it and read the cell off" presupposes the cell it was supposed to produce.

**Guessing is possible, and the guess is checkable, which is the half's whole cost.** The
adversary writes `tweakableInput publicSeed addr payload` with a payload it hopes is the cell.
Inside the handler that teaches it nothing: a canonical answer is served only where
`OpenCache.openCache publicSeed (availableAt state) table` has one, which by `hclosed` is only
where every child is available, so at an unavailable node it draws fresh, and a lucky guess
lower down cannot cascade upward either, since serving the node above needs the node below
available. But the handler is not the adversary's only source. A FORS signature **publishes**
the level-0 sibling `F(PK.seed ‖ ADRS ‖ sk)` of a secret it did not reveal and whose cell is
unavailable: the adversary queries `F(PK.seed ‖ ADRS ‖ x)` for a candidate `x` and compares with
that published sibling. One query per candidate, and on a hit it places the recovered secret
among its claims and `InputBad` holds with certainty.

**So `hclosed` does not make the charge a constant, and nothing else does either.** The `259`
claims `InputBad` quantifies over are the forgery's *outputs*; a guess that can be checked costs
the adversary its queries, and counting outputs instead is wrong by a factor of `q`.
`InputBullet` at the end of this file therefore pays
`expected (card recordAiming) + 259` over `2 ^ 128`, with the expected count paying for exactly
these tests. `InputBullet.bullet_of_bound` keeps the constant-hypothesis implication, because it
is true and costs nothing; what is false is that anything proves its hypothesis, and in
particular `hclosed` does not. -/

/-! ## The shape this half owes the join

Pinned by elaboration rather than by eye, because a mismatch between what an owner proves and
what the join takes is the failure that has cost this development most.

**The per-walk adapter is not available to this half**, and for the reason the obligation was
moved to the paired run in the first place: conditioning on the walk fixes the cell table, and
an adversary chosen knowing it makes the input event certain at that walk. So what this half
owes is `prob_sharedBad_le_expected`'s `hinput` itself, at the recorded **paired** run, with the
count the record's aiming part. `SharedJoin.hinput_of_probesIn` is for an owner whose charge is
per-walk; the ordering defect is such an owner and this one is not. -/

end SlhDsaSecurity.ProbeContainment
