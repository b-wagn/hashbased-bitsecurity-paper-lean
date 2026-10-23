import SlhDsaSecurity.Proof.Obligations
import SlhDsaSecurity.Proof.AnswerSide

/-!
# The answer obligation, from the pieces that are left

`SharedJoin.sharedCharged_of_parts` closes the shared obligation from its charges taken as
hypotheses, in the shapes their owners produce. This is the same thing for the answer half, and
for the same reason: three owners are building toward these shapes, and a mismatch between what
one produces and what another consumes should surface here rather than at assembly.

What is left is four things, and each is a hypothesis below:

* `hlate` — the ordering defect, as a support hypothesis on the recorded run;
* `hleftBound` — the disclosing cap, at `signingLimit`, which is its served-indexed form: one
  entry per served request, so the cap is the signing limit and not a growth bound;
* `hseed` — the narrowing's leftover, as the term the caller adds;
* and the tests, which stay parameters, so that the serving-flag presentation moves the
  *state type* in two hypotheses and nothing else.

## Where this side reads its counts, and why it differs from the other

The answer half reads its counts at the **split-counted presentation**, not at the record. Its
two charges partition the queries — a structural collision is witnessed outside the message
class and a coverage target inside it — so `ClassGrowth.splitCost` charges each query to exactly
one slot and `ClassGrowth.countAllHashes_eq_readOff` converts the pair back to the run's own
count. Nothing is lost in the conversion and no query is charged twice.

The shared half cannot do that, and the reason is not a preference: growth cannot report a
sensitive probe answered from the warm table, so its charges have to be read at the record,
where such a probe is visible. The two halves therefore read their counts off different
objects, each for a reason particular to it. The next reader will notice the asymmetry; this is
what it is.

## One thing a producer can get wrong and this file cannot catch

The two recorder hypotheses pin their key at `SplitCharged.generatedKey … walk.2` — the key the
**walk's** cache generates. The recorder's tests cannot be pinned anywhere else, since they are
fixed before the run; but the *charged event* can, and a charge stating `LateDisclosure` at
`SplitCharged.generatedKey … result.2.1` — the key the **run's** cache generates — does not
unify with what is asked here, and both statements look right read on their own. The two keys
are equal only on the support, by `AnswerSide.generatedKey_eq_walk`. A producer that reaches for
the run's key needs that lemma; a producer that uses the walk's key needs nothing.

## The one hypothesis that is not like the others

`hseed` asks for the leftover to be small **at a fixed walk**, and that is where it has to be
asked if the obligation is to stay in its present shape, because `AnswerCharged` is read at a
fixed walk. It is also where it cannot be answered: `SplitWitness.SeedRandomised` says the cache
holds a message input whose randomiser is `SK.prf`, the two byte formats coincide
(`FramingLeak.randomizerInput_eq_messageInput`: `randomizerInput prf PK.seed (PK.root ‖ m)` *is*
`messageInput prf pk m`), and at a fixed walk `SK.prf` is a constant an adversary may carry — so
one query at `messageInput SK.prf pk m` makes the event hold with probability one. That input is
message-class by construction and `PRF_msg`-class at the real seed by the identity, which is both
halves of `SeedRandomised`. No allowance, `2 ^ -126` or otherwise, survives it.

The hypothesis is stated anyway, because stating it is what makes the gap a shape question with
an answer rather than a surprise. The answer is the shared half's: the leftover belongs at
`Target.pairedRun`, where the seed is still random, which means it has to leave `AnswerBad`
rather than be paid inside it.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.AnswerJoin

open Security CanonicalGraph WarmedGame RoutedSplit Target AnswerSide

attribute [local irreducible] WarmedGame.afterSeeds Scheme.verify Scheme.keygenInternal
  Scheme.sign Security.signingOracle Security.countQueries

set_option linter.constructorNameAsVariable false

/-- The recorded run the two recorder hypotheses are read at: the game's own tail computation,
recorded.

**This is the shape the producers state at, and that is why it is this one.** Every lemma in
`SplitWitness` takes `computation : OracleComp OracleWorld (Outcome × Nat)` and
`SplitWitness.LateDisclosure`'s domain is `(Outcome × Nat) × SplitState`, so a charge proved
there plugs in with no adapter. The charge *consuming* these hypotheses reads the split-counted
run instead, and the two are bridged inside the proof by
`CoverageCount.mem_support_recorder_countAllHashes` — on this side, once, rather than at each
producer.

It takes no counter slots, which is the point: nothing a producer writes has to mention them,
so the presentation may renumber them freely. -/
noncomputable def answerRecordedRun (adversary : Adversary)
    (walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) :
    ProbComp ((Outcome × Nat) × SplitPrefix.SplitState) :=
  BlockViews.recordedRun
    (SplitWitness.disclosingKeep walk.1.1.2.1
      (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2))
    (SplitWitness.targetKeep walk.1.1.2.1
      (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2))
    (countAllHashes (afterSeeds adversary walk.1.1)) walk.2

/-! ## The same join, in the shape the restated target asks for

The target moved: the answer half is now read at `FusedCoverage.fusedTail` with the ordering
defect ruled out *pointwise* rather than assumed of the support, and
`AnswerShape.answerChargedLate_of_recordedBound` takes it at this file's own recorded run. Two
of the three hypotheses above survive unchanged; `hlate` does not survive at all, because it is
no longer a hypothesis — its negation is a conjunct of the charged event, and the whole point of
charging the defect on the shared side is that the set it describes is **not** empty.

`hseed` survives, and the module docstring above still says why it cannot be answered where it
is asked. It is kept in this shape so that the one remaining gap is a single named hypothesis
rather than a hole in the middle of a proof; the weakened cover
(`ObligationShapes.cover_of_served_or_narrow`) is what will retire it, by needing the narrowed
class at the forgery's own digest alone instead of at every cached message input — and that is a
change to `SplitWitness.Served.mem_records_of_covered`, not to anything here.

The bound is unchanged to the digit: the `2 ^ -126` the answer side never spent is what pays for
the leftover, and the ordering defect costs this side nothing because it is charged elsewhere. -/

/-! ## The same bound with no `hseed` at all

`answerRecordedBound_of_parts` still takes the leftover as a probability bound at a fixed walk,
where it has none. The repair is the one `hlate` already had: make it a **conjunct** and let the
shared half charge the complement where the seed is still random.

What makes that statable here and not for the disclosing cap is what the event is quantified over.
`SplitWitness.SeedRandomised` ranges over the whole cache, so it cannot leave this side at all
without a `q`-shaped charge, and the ledger's `q` coefficient is exactly two with both units
spent. `AnswerCoverage.ForgerySeedRandomised` names the **forgery's** published randomiser — one
object — so it can be moved to the paired run, where the seed is still random and the charge is
`ObligationShapes.sharedChargedLate_of_parts`' `seedUnits`, taken out of the shared side's claims.

**`seedUnits` is not `1`.** An earlier version of this paragraph said the forgery's randomiser was
one guess at a secret the signer never publishes;
`ObligationShapes.publishedRandomizer_eq_truncate` refutes that — the published randomiser is
`Hashing.truncate` of the answer at the seed's own `PRF_msg` input, so a single signing request
makes the secret testable one candidate per query.

The bound is unchanged to the digit, including the `2 ^ -126` this side still does not spend; it
is stated so that the restated `Obligations.AnswerChargedLate` consumes it without an adapter. -/

set_option maxHeartbeats 1000000 in
/-- **The answer half's bound with both unpayable clauses conjoined.** No probability hypothesis
at a fixed walk survives: the ordering defect and the narrowed leftover are both conjuncts, and
both complements are the shared half's. -/
theorem answerRecordedBound_narrow_of_parts {inside outside : QueryKind} (hne : inside ≠ outside)
    (hjoinNarrow : ∀ (adversary : Adversary)
      (walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec),
      walk ∈ support graphWalk → GoodWalk walk →
      ∀ result ∈ support (BlockViews.recordedRun
        (SplitWitness.disclosingKeep walk.1.1.2.1
          (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2))
        (SplitWitness.targetKeep walk.1.1.2.1
          (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2))
        (countQueries (ClassGrowth.splitCost (CombinedCharge.IsMessageInput
            (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2))
          inside outside) (afterSeeds adversary walk.1.1)) walk.2),
        SplitWitness.CoveredAtKeep walk.1.1.2.1
            (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2)
            ((result.1.1, result.1.2 inside + result.1.2 outside), result.2.1) →
          ¬ AnswerCoverage.ForgerySeedRandomised walk.1.1.2.1
            (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2)
            ((result.1.1, result.1.2 inside + result.1.2 outside), result.2.1) →
          ¬ SplitWitness.LateDisclosure walk.1.1.2.1
            (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2)
            ((result.1.1, result.1.2 inside + result.1.2 outside), result.2) →
          BlockViews.TargetCovered result)
    (hleftBound : ∀ (adversary : Adversary)
      (walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec),
      walk ∈ support graphWalk → GoodWalk walk →
      ∀ result ∈ support (answerRecordedRun adversary walk),
        result.2.2.1.length ≤ signingLimit)
    (hdisclosing : ∀ (adversary : Adversary)
      (walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec),
      walk ∈ support graphWalk → GoodWalk walk →
      ∀ result ∈ support (answerRecordedRun adversary walk), ∀ input : Bytes,
        ServedLog.servedLog
            (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2)
            (result.1, result.2.1) input ↔
          SplitWitness.disclosingKeep walk.1.1.2.1
            (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2)
            input result.2.1) :
    ∀ (q : Nat) (adversary : Adversary), 1 ≤ q → HasTotalBudget adversary q →
      ∀ walk ∈ support graphWalk, GoodWalk walk →
        Pr[fun result : (Outcome × Nat) × SplitPrefix.SplitState =>
            AnswerBad ((walk.1, result.1), result.2.1) ∧
              ¬ AnswerCoverage.ForgerySeedRandomised walk.1.1.2.1
                (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2)
                (result.1, result.2.1) ∧
              ¬ SplitWitness.LateDisclosure walk.1.1.2.1
                (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2) result |
          answerRecordedRun adversary walk] ≤
          (q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
            (1 : ℝ≥0∞) / ((2 ^ 141 : Nat) : ℝ≥0∞) := by
  classical
  intro q adversary _ hbudget walk hwalk hgood
  refine le_trans (prob_answerBad_good_le_of_caps_recorded_narrow adversary q hne hbudget hwalk
    hgood.2 signingLimit ForsLeaveOneOut.signingLimit_le_tapeBound
    (hjoinNarrow adversary walk hwalk hgood)
    (fun result hmem => hleftBound adversary walk hwalk hgood _
      (CoverageCount.mem_support_recorder_countAllHashes _ _ _ hne
        (afterSeeds adversary walk.1.1) (walk.2, [], []) result hmem))
    (hdisclosing adversary walk hwalk hgood)) ?_
  rw [show ((2 ^ 141 : Nat) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ 141 from by push_cast; ring]

/-! ## The bound with the narrowed class a parameter, and the retirement it makes an `exact`

The answer half's leftover is one conjunct of `SplitWitness.narrowClass`, and its retirement is
commissioned. So the bound below leaves the class free and carries
`SplitWitness.Served.NarrowTarget` as a conjunct of the event. Two readings follow, and neither
is a rewrite of the other:

* at `SplitWitness.narrowClass` the conjunct **is** the leftover, and
  `answerRecordedBound_narrow_of_parts` above charges it;
* at `CombinedCharge.IsMessageInput` the conjunct holds of every result, by
  `AnswerCoverage.narrowTarget_messageClass`, so `answerRecordedBound_wide_of_parts` drops it and
  there is nothing left to charge — the event is `AnswerBad ∧ ¬ late` and the bound is unchanged
  to the digit, with the `2 ^ -126` unspent.

When the clause goes, the second is what the assembly instantiates. If the two ever disagree
about anything but the class, the second stops elaborating.

Both state `q / 2 ^ 128 + 1 / 2 ^ 141`, which is what they prove — `Target.answerDefectProved`.

**The disclosing cap is a parameter for the same reason.** `CarrierFiles.leftRecord_length_le_cap`
concludes at `5 * 2 ^ 62` — the concentration's own cap — and `signingLimit = 2 ^ 64` is
*smaller*, so a hypothesis hard-wired to `signingLimit` could **not** be discharged from it:
there is no `le_trans` in that direction. Taking `leftLength` free, with the concentration's cap
as the side condition, lets the carrier's own lemma land by `exact`, and `signingLimit` with
`ForsLeaveOneOut.signingLimit_le_tapeBound` is still available for a caller that has the log
length instead. -/

/-- The recorded run at a target class left free. At `SplitWitness.narrowClass` it is
`answerRecordedRun`, definitionally. -/
noncomputable def answerRecordedRunAt (narrow : Bytes → Prop) (adversary : Adversary)
    (walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) :
    ProbComp ((Outcome × Nat) × SplitPrefix.SplitState) :=
  BlockViews.recordedRun
    (SplitWitness.disclosingKeep walk.1.1.2.1
      (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2))
    (SplitWitness.Served.targetKeep (fun probe _ => narrow probe) (SplitWitness.disclosingKeep walk.1.1.2.1
      (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2)))
    (countAllHashes (afterSeeds adversary walk.1.1)) walk.2

/-- **At the class the game uses today, it is the run the obligation is read at.** -/
theorem answerRecordedRunAt_narrowClass (adversary : Adversary)
    (walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) :
    answerRecordedRunAt (SplitWitness.narrowClass walk.1.1.2.1
      (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2))
      adversary walk = answerRecordedRun adversary walk := rfl

end SlhDsaSecurity.AnswerJoin
