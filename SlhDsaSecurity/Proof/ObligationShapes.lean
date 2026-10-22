import SlhDsaSecurity.Proof.FinalAssembly
import SlhDsaSecurity.Proof.FramingLeak

/-!
# What the two obligations have to become

`FinalAssembly.target_of_producers` lists the six hypotheses the proof still rests on. Two of
them are not merely unproved, they are **false**, and this file says what replaces them, in
shapes rather than proofs. The two that are false are not false in the same way and do not have
the same repair.

## `hseed` is false, and relocating it would not help

`hseed` bounds `Pr[SplitWitness.SeedRandomised]`. That event says the cache holds an input that
is both message-class at the public key and a `PRF_msg` input at the real seed — and the signer
makes such a query itself. By `FramingLeak.randomizerInput_eq_messageInput`, the request framed
as `PK.root ‖ m` has `PRF_msg(SK.prf, PK.seed, PK.root ‖ m) = H_msg(SK.prf, PK.seed, PK.root, m)`
as *the same byte string*; `FramingLeak.exists_legal_request` says such a request is legal
whenever `PK.root` opens with a zero byte, which `FramingOverlap.keygen_zero_probability` puts at
exactly `1 / 256`. So the event is **certain** on a `1 / 256` slice of key generation, whatever
the adversary's budget. `seedRandomised_of_signer_query` below is that, proved, so the claim is
checkable rather than asserted.

No allowance carries a `2 ^ -8` term. The repair is not to move the charge but to stop making
it: `SeedRandomised` is a blunt over-approximation of what the coverage join actually loses to
the narrowing, and the join needs the narrowed class at exactly **one** input.

## Where the narrowing is really needed, and where it is not

`SplitWitness.Served.cover` asks for `narrow input` to conclude that the input is filed on one
side or the other. For an input the **left** test already keeps, that is more than is needed:
being disclosing is itself a reason to be filed, and the class never enters.
`cover_of_served_or_narrow` below is the weakened form, proved.

With it, the narrowed class is needed only at the **target** — the forgery's own digest input,
which is not disclosing by construction. So the whole leftover is one event: the forgery's
published randomiser is `SK.prf` itself, which is a guess at a secret the adversary never sees.
One unit of `2 ^ -128`, and the answer side's unspent `2 ^ -126` carries it with room to spare.

The witnesses' side of the old leftover — a served request's published randomiser being the seed
— disappears entirely, which matters, because that one is one unit *per served request* and the
signing limit is `2 ^ 64`.

## `hlate` is false, but its charge exists and is already proved

`hlate` says late disclosure never happens on the support. It happens; that is what it is charged
for. But `LateRate.prob_lateDisclosure_le` is a **per-walk** bound, so what sent the charge to the
shared side was never the randomness — it was the count. The count is the target recording's
length, which `LateProbes.probes_le_recordMessageClass` puts inside the record's message-class
part, and `LateProbes.prob_ordering_le` pays it there.

So `¬ Late` becomes a conjunct of the answer side's event and `Late` is paid once on the shared
side. The conjunct has to be expressible, which it is not at `WarmedGame.tail` — a tail result
carries no recordings — so both obligations are read at the fused presentation, where
`FusedCoverage.forgetsTo` carries every event that does not mention the recordings across
unchanged.

## The ledger, and it closes with both allowances unchanged

The answer side's `q / 2 ^ 128` is the two answer charges against one split counter, as before.
The shared side's `(q - 2 ^ subtreeHeight + 259) / 2 ^ 128` is, by `SharedJoin.card_parts_le_budget`,
room for the record's aiming part and its message-class part together, plus the claims. The input
half's bullet turns out to be claims-only, so it spends the `259` and **nothing of the record**.
That leaves both parts free, and the ordering defect needs one of them:

| term | where paid | count |
| --- | --- | --- |
| structural collision | answer | outside slot of the split counter |
| coverage | answer | inside slot of the split counter |
| forgery's randomiser is `SK.prf` | answer | one unit, inside the unspent `2 ^ -126` |
| the forgery's claims | shared | `259` |
| late disclosure | shared | the record's message-class part |
| — | — | the record's aiming part, unspent |

Two units per message-class entry were never needed: the second unit was the witnesses' half of
the seed leftover, and the weakened cover removes it. Neither allowance changes.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.ObligationShapes

open Security WarmedGame RoutedSplit Target SplitPrefix

/-! ## The two facts the design rests on -/

/-- **The signer's own `PRF_msg` query makes `SeedRandomised` hold.** On a request framed as
`PK.root ‖ m` the two byte formats coincide, so the signer's randomiser input is a message input
at randomiser `SK.prf` — message-class and `PRF_msg`-class at once, which is the whole event.
This is why the event cannot be charged at any `2 ^ -128` rate: `FramingLeak.exists_legal_request`
makes such a request legal on a `1 / 256` slice of key generation, and on it the adversary makes
the event certain by asking for one signature. -/
theorem seedRandomised_of_signer_query (prfSeed : Digest) (pk : PublicKey)
    (cache : QueryCache HashSpec) (message : Bytes)
    (hcached : cache (Hashing.randomizerInput prfSeed pk.seed (bytesBE n pk.root ++ message)) ≠
      none) :
    SplitWitness.SeedRandomised prfSeed pk cache :=
  ⟨Hashing.randomizerInput prfSeed pk.seed (bytesBE n pk.root ++ message), hcached,
    ⟨prfSeed, message, FramingLeak.randomizerInput_eq_messageInput prfSeed pk message⟩,
    ⟨pk.seed, bytesBE n pk.root ++ message, rfl⟩⟩

/-- **A guess at `SK.prf` is testable at one query**, which is why the forgery's published
randomiser is not a one-shot guess at a secret the adversary never sees.

The randomiser the signer publishes for a framing is `Hashing.truncate` of the oracle's answer
at `Hashing.randomizerInput SK.prf PK.seed framed` — that is this equation, and
`ReplayGate.randomizer_eq_of_replay` is the same fact about a *published* signature, read off
the log. An adversary holding one signature can therefore test a candidate `x` by asking at
`Hashing.randomizerInput x PK.seed framed` and comparing the truncation with what the signature
carries, at one query per candidate.

So "never sees it" is true and "cannot check a guess" is false, and the second is what would be
needed for a constant. The event's probability is the probability of *finding* the seed, which
is one unit of `2 ^ -128` per query and not one unit in total. `RandomiserDeferral`'s module
docstring is the same obstruction read from the other end: deferring the draw is necessary and
not sufficient, because the tail's signer derives every randomiser by querying at the seed, and
what closes that gap is an identical-until-bad hop whose bad flag is exactly a query at a
`PRF_msg` input at the real seed. -/
theorem publishedRandomizer_eq_truncate (cache : QueryCache HashSpec) (sk : SecretKey)
    (framed : Bytes) :
    HonestProbes.replayRandomizer cache sk framed =
      Hashing.truncate (CacheReplay.replay cache
        (Hashing.randomizerInput sk.prf sk.publicKey.seed framed)) := rfl

/-- **A disclosing input needs no class.** `SplitWitness.Served.cover` asks for the narrowed
class to conclude that an input is filed on one side or the other; an input the left test keeps
is filed for that reason alone. So the class is needed only where the left test fails, which in
the coverage join is the target and nothing else. -/
theorem cover_of_served_or_narrow (narrow : Bytes → Prop)
    (served : Bytes → QueryCache HashSpec → Prop) (input : Bytes)
    (cache : QueryCache HashSpec) (hcover : served input cache ∨ narrow input) :
    served input cache ∨ SplitWitness.Served.targetKeep narrow served input cache := by
  classical
  by_cases hserved : served input cache
  · exact Or.inl hserved
  · exact Or.inr ⟨hcover.resolve_left hserved, hserved⟩

/-! ## The shared half of the new shape is already proved

Nothing in `SharedAssembly`'s argument has to change for it: its proof already splits the shared
event by excluded middle and pays the ordering defect on the far side, so it proves the wider
event as it stands. Only the conclusion was narrower than what the target will need. That the
input half's bullet is claims-only costs nothing here either — a bullet that spends `259` and
none of the record satisfies a hypothesis that allows the aiming part besides. -/

set_option maxHeartbeats 1000000 in
/-- **The shared obligation at its adopted shape**, with the narrowing's leftover carried at
whatever it costs.

`seedUnits` is a parameter and not a numeral on purpose. The obligation's room is `claims`
units of `2 ^ -128`, of which the forgery's own claims take `259`, so a leftover that costs a
fixed number of units fits and one that costs a number growing with `q` does not — and at the
call site that is the difference between passing a numeral and being unable to. The shape
therefore records the question rather than answering it, which is the one thing a hypothesis
asserting `1 / 2 ^ 128` would not do. See the section below for why I believe the answer is the
second kind. -/
theorem sharedChargedLate_of_parts (claims seedUnits : Nat) (hclaims : 259 + seedUnits ≤ claims)
    (hinput : ∀ (q : Nat) (adversary : Adversary), HasTotalBudget adversary q →
      SharedAssembly.InputBullet adversary LateProbes.Ordering)
    (hsigner : ∀ adversary : Adversary, LateProvenance.SignerDigestFree adversary)
    (hseed : ∀ (q : Nat) (adversary : Adversary), HasTotalBudget adversary q →
      Pr[fun pair : LateProbes.SplitPair => GoodWalk pair.1 ∧
          AnswerCoverage.ForgerySeedRandomised pair.1.1.1.2.1
            (SplitCharged.generatedKey pair.1.1.1.1 pair.1.1.1.2.1 pair.1.1.1.2.2 pair.1.2)
            (FinalAssembly.forgetFused pair.2) |
        LateProbes.pairedOf FusedCoverage.fusedTail adversary] ≤
        ((seedUnits : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)) :
    Obligations.SharedChargedLate claims FusedCoverage.fusedTail FinalAssembly.forgetFused
      FinalAssembly.lateOrSeed := by
  classical
  intro q adversary _ hbudget
  have hforget := FusedCoverage.forgetsTo adversary
  have hprobes := LateProbes.probes_le_recordMessageClass hforget
    (FusedCoverage.isRecorderRun adversary)
    (LateProvenance.hrecord_of_signerDigestFree adversary (hsigner adversary))
  have hordering := LateProbes.prob_ordering_le (FusedCoverage.isRecorderRun adversary) hprobes
  refine le_trans (probEvent_mono (q := fun pair : LateProbes.SplitPair =>
    (GoodWalk pair.1 ∧ InputBad (SharedAssembly.splitTraceOf pair) ∧
        ¬ LateProbes.Ordering pair) ∨
      ((GoodWalk pair.1 ∧ LateProbes.Ordering pair) ∨
        (GoodWalk pair.1 ∧ AnswerCoverage.ForgerySeedRandomised pair.1.1.1.2.1
          (SplitCharged.generatedKey pair.1.1.1.1 pair.1.1.1.2.1 pair.1.1.1.2.2 pair.1.2)
          (FinalAssembly.forgetFused pair.2)))) ?_) ?_
  · rintro pair - ⟨hgood, hshared | hordered | hseeded⟩
    · exact (SharedJoin.cover_of_em
        (fun pair : LateProbes.SplitPair => InputBad (SharedAssembly.splitTraceOf pair))
        LateProbes.Ordering pair hshared).imp (fun hin => ⟨hgood, hin⟩) fun hord =>
          Or.inl ⟨hgood, hord⟩
    · exact Or.inr (Or.inl ⟨hgood, hordered⟩)
    · exact Or.inr (Or.inr ⟨hgood, hseeded⟩)
  refine le_trans (probEvent_or_le _ _ _) ?_
  refine le_trans (add_le_add (hinput q adversary hbudget)
    (le_trans (probEvent_or_le _ _ _)
      (add_le_add hordering (hseed q adversary hbudget)))) ?_
  rw [← add_assoc, ENNReal.div_add_div_same, ENNReal.div_add_div_same]
  refine ENNReal.div_le_div_right ?_ _
  calc (ClassExpectation.expected (LateProbes.pairedOf FusedCoverage.fusedTail adversary)
          (fun pair =>
            Multiset.card (SharedJoin.recordAiming (LateProbes.forgetRecordings pair))) +
        ((259 : Nat) : ℝ≥0∞) +
        ClassExpectation.expected (LateProbes.pairedOf FusedCoverage.fusedTail adversary)
          (fun pair =>
            Multiset.card (SharedJoin.recordMessageClass (LateProbes.forgetRecordings pair)))) +
        ((seedUnits : Nat) : ℝ≥0∞)
      = ClassExpectation.expected (LateProbes.pairedOf FusedCoverage.fusedTail adversary)
            (fun pair =>
              Multiset.card (SharedJoin.recordAiming (LateProbes.forgetRecordings pair))) +
          ClassExpectation.expected (LateProbes.pairedOf FusedCoverage.fusedTail adversary)
            (fun pair =>
              Multiset.card (SharedJoin.recordMessageClass (LateProbes.forgetRecordings pair))) +
          ((259 + seedUnits : Nat) : ℝ≥0∞) := by push_cast; ring
    _ ≤ ((q - 2 ^ subtreeHeight : Nat) : ℝ≥0∞) + ((claims : Nat) : ℝ≥0∞) :=
        add_le_add (SharedAssembly.expected_parts_le_budget q adversary hbudget)
          (Nat.cast_le.mpr hclaims)
    _ = ((q - 2 ^ subtreeHeight + claims : Nat) : ℝ≥0∞) := (Nat.cast_add _ _).symm

/-! ## Why `seedUnits` is a parameter and not `1`

The leftover is `AnswerCoverage.ForgerySeedRandomised`: the forgery's published randomiser is
`SK.prf`. The reading that makes it a constant is that the forgery is one object and `SK.prf` a
secret the adversary never sees, so it is one guess. **The first half is true and the second does
not follow, because a guess is checkable.**

`publishedRandomizer_eq_truncate` is the check: the randomiser the signer publishes for a
framing is `Hashing.truncate` of the oracle's answer at `Hashing.randomizerInput SK.prf PK.seed
framed`. So an adversary that asks for one signature, on any framing at all, can test a
candidate `x` by querying at `Hashing.randomizerInput x PK.seed framed` and comparing the
truncation with what that signature carries. Each candidate costs one query, a hit identifies
the seed, and the forgery then publishes it. The event's probability is the probability of
*finding* the seed, which is one unit of `2 ^ -128` per query — `q`-shaped, not constant.

The same thing seen from the formal side: a constant can only come from an identical-until-bad
hop against a game that does not read the seed, which is `HandlerComparison.prob_bad_eq`, and
its bad flag is *a query at a `PRF_msg` input at the real seed*. `RandomiserDeferral`'s module
docstring states the obstruction in those terms already — deferring the draw past the walk is
necessary and **not sufficient**, because the tail's signer derives every randomiser by querying
at the seed. The flag's probability is the randomiser defect's, which the two-way split retired
and for which the budget has no room: `Target.allowanceOf`'s `Nat` line is `2 * q` with one `q`
on each half.

So `seedUnits` stays a parameter. A caller with a constant bound passes a numeral and
`hclaims : 259 + seedUnits ≤ claims` fits inside the `247` units `allowanceOf` leaves; a caller
with a `q`-shaped bound finds it cannot, which is the obstruction made visible rather than
assumed away.

**Where I would look instead of for a bound.** The leftover only arises through the FIPS 205
format identity, which makes the signer's own randomiser query a *message* input; and in the
case where it bites, the forgery's digest input was first queried by the signer, so its answer
was drawn inside the signer and only its truncation was ever published. The digest itself is a
uniform value the adversary has not seen — which is exactly the position the coverage charge is
designed for. The case is therefore a bookkeeping gap rather than a probability one: the
recorder files on fresh draws, and this draw was not the adversary's. That points at the
recorder's filing seeing the signer, not at a charge. -/

/-! ## The whole of it, from what is still owed

One hypothesis of the three below is an obligation and two are leaves. The obligation is the
answer half's, restated with late disclosure ruled out; the leaves are the input half's bullet
and the provenance branch the carrier's test retires. Nothing else is assumed. -/

/-- **The target, from the answer obligation and the shared half's three leaves.** -/
theorem target_of_answer_and_leaves (claims seedUnits : Nat)
    (hclaims : 259 + seedUnits ≤ claims) (hfits : claims + 6 ≤ 2 ^ subtreeHeight)
    (hanswer : Obligations.AnswerChargedLate FusedCoverage.fusedTail FinalAssembly.forgetFused
      FinalAssembly.lateOrSeed)
    (hinput : ∀ (q : Nat) (adversary : Adversary), HasTotalBudget adversary q →
      SharedAssembly.InputBullet adversary LateProbes.Ordering)
    (hsigner : ∀ adversary : Adversary, LateProvenance.SignerDigestFree adversary)
    (hseed : ∀ (q : Nat) (adversary : Adversary), HasTotalBudget adversary q →
      Pr[fun pair : LateProbes.SplitPair => GoodWalk pair.1 ∧
          AnswerCoverage.ForgerySeedRandomised pair.1.1.1.2.1
            (SplitCharged.generatedKey pair.1.1.1.1 pair.1.1.1.2.1 pair.1.1.1.2.2 pair.1.2)
            (FinalAssembly.forgetFused pair.2) |
        LateProbes.pairedOf FusedCoverage.fusedTail adversary] ≤
        ((seedUnits : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)) :
    HasTotalSecurityBits .strong 127 :=
  FinalAssembly.target_of_producers claims hfits hanswer
    (sharedChargedLate_of_parts claims seedUnits hclaims hinput hsigner hseed)

/-! ## `hsigner` is false, and it is false for a reason worth writing down

`LateProvenance.SignerDigestFree` says no target-recorded input is a request's own digest
input. Its docstring's justification is right — such a query is signer-randomised **when it is
made**, so the left test takes it — but the statement reads the randomiser off the **final**
cache, through `HonestProbes.replayRandomizer`. The two differ exactly where the adversary
queries a digest input before the request that would make it served, which is the case the
ordering defect exists for.

Worse, `CacheReplay.replay` answers a miss with `default`, so on a message that is never signed
the replayed randomiser is a value the adversary knows. The two theorems below are the two steps
of a one-query refutation:

* `targetKeep_default` — the input `messageInput (truncate default) pk m` is target-recorded at
  any cache holding no `PRF_msg` entry at the real seed. It is message-class by construction,
  it is outside the `PRF_msg` class unless `truncate default` is `SK.prf` itself, and it cannot be
  signer-randomised at a cache with no `PRF_msg` entry to randomise it.
* `messageInput_default_eq_replay` — at such a cache that input **is**
  `messageInput (replayRandomizer cache sk m) pk m`.

So an adversary that queries that one input, for a message it never has signed, produces a
target-recorded entry that `SignerDigestFree` forbids. No carrier, no ordering, no budget.

The escape clause is narrower than it looks: `¬ PrfClass` fails only when `truncate default` is
`SK.prf` itself, by injectivity of the format through `FramingLeak.randomizerInput_eq_messageInput`
— a `2 ^ -128` event, not the `1 / 256` legality coincidence, which gates whether `PK.root ‖ m` is
a legal frame and so never arises for an adversary that makes no signing request. What is
kernel-checked here is the pair of predicate facts; that such an entry lands in a real run's
target recording needs freshness at the walk cache and `hcold` at that run's final cache, both
routine for a one-query adversary that signs nothing and neither of them in Lean. The hypothesis
is refuted, not proved false.

**What this does not threaten is the consequence.** `LateProvenance.hrecord_of_signerDigestFree`
only wants every target-recorded input to be in `SharedJoin.recordOf` — the adversary's and the
verifier's own queries — and the refuting input is an adversary query, so it is in the record.
The hypothesis is a sufficient condition far stronger than what it is used for, and the repair
is to prove the consequence by provenance instead: the signer's canonical probes are not
message-class, its randomiser probe is removed by `narrowClass`'s `PRF_msg` clause, and its
digest probe is signer-randomised at the state it is made at. Only the last needs the signer's
two probes **in order**, which is where the honest statement lives. -/

/-- **The input a one-query adversary files as a target.** Message-class by construction, and
not signer-randomised at a cache that holds no `PRF_msg` entry at the real seed. -/
theorem targetKeep_default (prfSeed : Digest) (pk : PublicKey) (cache : QueryCache HashSpec)
    (message : Bytes)
    (hprf : ¬ RandomizerGate.PrfClass prfSeed
      (Hashing.messageInput (Hashing.truncate (default : HashOutput)) pk message))
    (hcold : ∀ m : Bytes, cache (Hashing.randomizerInput prfSeed pk.seed m) = none) :
    SplitWitness.targetKeep prfSeed pk
      (Hashing.messageInput (Hashing.truncate (default : HashOutput)) pk message) cache := by
  refine ⟨⟨⟨Hashing.truncate (default : HashOutput), message, rfl⟩, hprf⟩, ?_⟩
  rintro ⟨m, answer, hcached, -⟩
  rw [hcold m] at hcached
  exact absurd hcached (by simp)

/-- **And at that same cache it is the replayed digest input the hypothesis forbids.** -/
theorem messageInput_default_eq_replay (cache : QueryCache HashSpec) (sk : SecretKey)
    (message : Bytes)
    (hmiss : cache (Hashing.randomizerInput sk.prf sk.publicKey.seed message) = none) :
    Hashing.messageInput (Hashing.truncate (default : HashOutput)) sk.publicKey message =
      Hashing.messageInput (HonestProbes.replayRandomizer cache sk message) sk.publicKey
        message := by
  rw [HonestProbes.replayRandomizer, CacheReplay.replay, hmiss, Option.getD_none]

end SlhDsaSecurity.ObligationShapes
