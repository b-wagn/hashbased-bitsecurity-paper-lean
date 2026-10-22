import SlhDsaSecurity.Proof.LateProbes
import SlhDsaSecurity.Proof.RandomiserRecord

/-!
# The tail the ordering term reads, and the two equations it owes

`LateProbes` asks a fused presentation for two things and nothing else: that its tail **is** a
recorder run at the walk's own cache and key, and that forgetting its recordings leaves the
recorded paired run. This file supplies both, and the tail that does it is the one already in
hand — `RecordedTail.recordedAfterSeeds` run under `SplitPrefix.recorder` instead of under the
shared oracle.

Nothing is reshaped. The value is `RecordedTail.recordedTail`'s, so the adversary-and-verifier
record stays the `Multiset Bytes` beside the `Outcome` and `SharedJoin.recordOf` reads it
unchanged; the state is the recorder's own `SplitState`, disclosing recording first and target
second, in the position `StateT` already puts it. The two recordings stay **lists**: the
potential argument reads the cache in force when an entry was filed and counts the recording's
length, and a multiset of the same inputs is a different object no projection recovers them
from.

**Forgetting is an equality of computations, not merely of distributions.** `ForgetsTo` asks only
for the pointwise probabilities and a support containment, because the two runs were expected to
be different computations — but they are not. The recorder answers every query exactly as the
shared oracle does and appends to its recordings afterwards, so dropping the recordings returns
the shared oracle's run on the nose. `run_recorder_forget` is that, by one induction, and both
conjuncts fall out of it.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.FusedCoverage

open Security SplitPrefix

/-! ## Dropping the recordings -/

set_option maxHeartbeats 800000 in
/-- **The recorder is the shared oracle with two recordings alongside.** Dropping them returns
the shared oracle's run, as an equality of computations. -/
theorem run_recorder_forget (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    {α : Type} (computation : OracleComp OracleWorld α) :
    ∀ state : SplitState,
      (fun z : α × SplitState => (z.1, z.2.1)) <$>
          (simulateQ (recorder leftKeep rightKeep) computation).run state =
        (simulateQ KeygenUniform.rom computation).run state.1 := by
  classical
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state
    rw [simulateQ_pure, StateT.run_pure, simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind queried next ih =>
    intro state
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, simulateQ_bind,
      simulateQ_spec_query, StateT.run_bind, map_bind]
    rcases queried with coin | input
    · rw [recorder_run_inl, DigestTape.rom_run_inl, bind_assoc, bind_assoc]
      refine bind_congr fun value => ?_
      rw [pure_bind, pure_bind]
      exact ih value state
    · rw [recorder_run_inr, DigestTape.rom_run_inr, bind_assoc]
      refine bind_congr fun step => ?_
      rw [pure_bind]
      exact ih step.1 (step.2, appended leftKeep rightKeep input state step.1)

/-! ## The tail -/

/-- The two tests the answer side's join names, at a walk. -/
noncomputable abbrev leftKeepAt
    (walk : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec) :
    Bytes → QueryCache HashSpec → Prop :=
  SplitWitness.disclosingKeep walk.1.1.2.1
    (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2)

/-- The target test at a walk. -/
noncomputable abbrev rightKeepAt
    (walk : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec) :
    Bytes → QueryCache HashSpec → Prop :=
  SplitWitness.targetKeep walk.1.1.2.1
    (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2)

/-- **The tail the ordering term reads**: the recorded game, run under the recorder. -/
noncomputable def fusedTail : LateProbes.FusedTail :=
  fun adversary walk =>
    (simulateQ (recorder (leftKeepAt walk) (rightKeepAt walk))
      (countAllHashes (RecordedTail.recordedAfterSeeds adversary walk.1.1))).run
        (walk.2, [], [])

/-- **It is a recorder run at the walk's own cache and key.** -/
theorem isRecorderRun (adversary : Adversary) :
    LateProbes.IsRecorderRun fusedTail adversary :=
  fun walk _ => ⟨countAllHashes (RecordedTail.recordedAfterSeeds adversary walk.1.1), rfl⟩

/-- **Forgetting its recordings leaves the recorded tail**, as an equality of computations. -/
theorem forget_fusedTail (adversary : Adversary)
    (walk : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec) :
    (fun z : (((Outcome × Multiset Bytes) × Nat) × SplitState) => (z.1, z.2.1)) <$>
        fusedTail adversary walk =
      RecordedTail.recordedTail adversary walk := by
  rw [fusedTail, RecordedTail.recordedTail,
    run_recorder_forget (leftKeepAt walk) (rightKeepAt walk) _ (walk.2, [], [])]

/-- **And so at the paired run**, which is both conjuncts of what `LateProbes` asks. -/
theorem forgetsTo (adversary : Adversary) : LateProbes.ForgetsTo fusedTail adversary := by
  have hmap : LateProbes.forgetRecordings <$> LateProbes.pairedOf fusedTail adversary =
      RandomiserRecord.recordedPairedRun adversary := by
    rw [LateProbes.pairedOf, RandomiserRecord.recordedPairedRun, map_eq_bind_pure_comp,
      bind_assoc]
    refine bind_congr fun walk => ?_
    rw [← forget_fusedTail adversary walk, map_eq_bind_pure_comp, bind_assoc, bind_assoc]
    refine bind_congr fun result => ?_
    simp [Function.comp_def, LateProbes.forgetRecordings]
  exact ⟨fun pair => by rw [hmap], by rw [hmap]⟩

end SlhDsaSecurity.FusedCoverage
