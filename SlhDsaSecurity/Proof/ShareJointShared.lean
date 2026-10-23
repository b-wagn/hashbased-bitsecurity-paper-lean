import SlhDsaSecurity.Proof.ShareJointBound
import SlhDsaSecurity.Proof.JointBudget
import SlhDsaSecurity.Proof.BySourceShared

/-!
# The shared half on accepted forgeries

`BySourceShared.hshared` at the adversary's own work. The event carries an accepted forgery, and
the chain is the same three links with the jointly capped games in place of the old ones:

* the real event with an accepted forgery is at most as likely in the jointly capped real game
  (`JointBudget.probEvent_realFlat_le`, at `limit = q - 569`);
* that is at most the lenient flag, and so the blind flag (`SetupBound`, the coupling of
  `ShareJointCouple` read through the event lemmas);
* the blind flag is at most the charged entries over `2 ^ 128`, at most `q - 569 + 330 + 231 =
  q - 8` of them (`ShareJointBound.charged_blindRun_shareCompJ`).
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.ShareJointShared

open Security CanonicalGraph WarmedGame WalkTable TableTail RecordedQueries RecordedPhase
  SharePresent ShareGame BySourceBridge

attribute [local irreducible] WarmedGame.afterSeeds Scheme.verify Scheme.keygenInternal
  Security.countQueries

/-- **The per-setup link**: at a good setup, the real event with an accepted forgery in the
jointly capped real game is at most the blind flag of the jointly capped game. -/
def SetupBound (adversary : Adversary) (limit : Nat) : Prop :=
  ∀ setup : Setup, setup.Good →
    Pr[fun r => ShareFinal.RealEvent setup r ∧ r.1.1.2.1 = true |
        ShareJoint.realFlatJ adversary limit (setup.sk, setup.pk) setup.warm] ≤
      Pr[fun z => z.2.2 = true | ShareBound.flagRun (ShareJoint.shareCompJ adversary limit) setup]

set_option maxHeartbeats 4000000 in
/-- **At one walk, the shared event on an accepted forgery is at most the blind flag.** -/
theorem walk_bound {adversary : Adversary} {q : Nat} (hbudget : TailBudgetW adversary q)
    (hsetup : SetupBound adversary (q - 569))
    (prfSeed publicSeed : Digest) (table : Cells × Padding) :
    Pr[fun result => Target.GoodWalk (WalkTable.walkOfTable prfSeed publicSeed table) ∧
        (RoutedSplit.InputBad (SharedJoin.recordedTraceOf
            (WalkTable.walkOfTable prfSeed publicSeed table, result)) ∨
          Target127.Late (WalkTable.walkOfTable prfSeed publicSeed table, result)) ∧
        result.1.1.1.verified = true |
      RecordedTail.recordedTail adversary (WalkTable.walkOfTable prfSeed publicSeed table)] ≤
      Pr[fun z => (ShareFinal.setupOf prfSeed publicSeed table).Good ∧ z.2.2 = true |
        ShareBound.flagRun (ShareJoint.shareCompJ adversary (q - 569))
          (ShareFinal.setupOf prfSeed publicSeed table)] := by
  classical
  by_cases hgood : (ShareFinal.setupOf prfSeed publicSeed table).Good
  · refine le_trans (probEvent_mono fun result _ hevent => hevent.2) ?_
    have hlinked := SharePresent.probEvent_recordedTail_linked adversary prfSeed publicSeed table
      (fun x => (RoutedSplit.InputBad (SharedJoin.recordedTraceOf
          (WalkTable.walkOfTable prfSeed publicSeed table, ((x.1, 0), x.2))) ∨
        Target127.Late (WalkTable.walkOfTable prfSeed publicSeed table, ((x.1, 0), x.2))) ∧
        x.1.1.verified = true)
    refine le_trans (le_of_eq hlinked) ?_
    rw [SharePresent.linkedRun_eq]
    refine le_trans (le_trans ?_ (JointBudget.probEvent_realFlat_le hbudget prfSeed publicSeed
      table (fun r => ShareFinal.RealEvent (ShareFinal.setupOf prfSeed publicSeed table) r ∧
        r.1.1.2.1 = true))) ?_
    · exact probEvent_mono fun r _ h => ⟨h, h.2⟩
    · rw [TouchedKeys.keysOf_eq]
      exact le_trans (hsetup (ShareFinal.setupOf prfSeed publicSeed table) hgood)
        (probEvent_mono fun z _ hz => ⟨hgood, hz⟩)
  · refine le_trans (le_of_eq (probEvent_eq_zero fun result _ hevent =>
      hgood ((ShareFinal.goodWalk_iff prfSeed publicSeed table).mp hevent.1))) (by simp)

open BlindCharge in
set_option maxHeartbeats 4000000 in
/-- **The shared half on accepted forgeries, key generation's and the signer's calls free.** -/
theorem hshared (q : Nat) (adversary : Adversary) (hbudget : TailBudgetW adversary q)
    (hq : 569 ≤ q) (hsetup : SetupBound adversary (q - 569))
    (hfiles : ∀ setup : Setup, ShareJointBound.VerifierFiles setup) :
    Pr[fun pair : SharedJoin.RecordedPair => Target.GoodWalk pair.1 ∧
        (RoutedSplit.InputBad (SharedJoin.recordedTraceOf pair) ∨ Target127.Late pair) ∧
        pair.2.1.1.1.verified = true |
      RandomiserRecord.recordedPairedRun adversary] ≤
      ((q - 8 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (RecordedWalkTable.evalDist_recordedPairedRun adversary)]
  calc Pr[fun pair : SharedJoin.RecordedPair => Target.GoodWalk pair.1 ∧
          (RoutedSplit.InputBad (SharedJoin.recordedTraceOf pair) ∨ Target127.Late pair) ∧
          pair.2.1.1.1.verified = true |
        (do
          let prfSeed ← ($ᵗ Digest : ProbComp Digest)
          let publicSeed ← ($ᵗ Digest : ProbComp Digest)
          RecordedWalkTable.recordedTableRun adversary prfSeed publicSeed)]
      = ex ($ᵗ Digest : ProbComp Digest) fun prfSeed => ex ($ᵗ Digest : ProbComp Digest)
          fun publicSeed => ex ($ᵗ (Cells × Padding) : ProbComp (Cells × Padding)) fun table =>
            Pr[fun result => Target.GoodWalk (WalkTable.walkOfTable prfSeed publicSeed table) ∧
                (RoutedSplit.InputBad (SharedJoin.recordedTraceOf
                    (WalkTable.walkOfTable prfSeed publicSeed table, result)) ∨
                  Target127.Late (WalkTable.walkOfTable prfSeed publicSeed table, result)) ∧
                result.1.1.1.verified = true |
              RecordedTail.recordedTail adversary
                (WalkTable.walkOfTable prfSeed publicSeed table)] := by
        rw [probEvent_eq_ex_bind]
        refine ex_congr _ fun prfSeed => ?_
        rw [probEvent_eq_ex_bind]
        refine ex_congr _ fun publicSeed => ?_
        rw [RecordedWalkTable.recordedTableRun, probEvent_eq_ex_bind]
        refine ex_congr _ fun table => ?_
        rw [bind_pure_comp, probEvent_map]
        rfl
    _ ≤ ex ($ᵗ Digest : ProbComp Digest) fun prfSeed => ex ($ᵗ Digest : ProbComp Digest)
          fun publicSeed => ex ($ᵗ (Cells × Padding) : ProbComp (Cells × Padding)) fun table =>
            Pr[fun z => (ShareFinal.setupOf prfSeed publicSeed table).Good ∧ z.2.2 = true |
              ShareBound.flagRun (ShareJoint.shareCompJ adversary (q - 569))
                (ShareFinal.setupOf prfSeed publicSeed table)] :=
        ex_mono _ fun prfSeed => ex_mono _ fun publicSeed => ex_mono _ fun table =>
          walk_bound hbudget hsetup prfSeed publicSeed table
    _ = ex ($ᵗ Digest : ProbComp Digest) fun publicSeed => ex ($ᵗ Digest : ProbComp Digest)
          fun prfSeed => ex ($ᵗ (Cells × Padding) : ProbComp (Cells × Padding)) fun table =>
            Pr[fun z => (ShareFinal.setupOf prfSeed publicSeed table).Good ∧ z.2.2 = true |
              ShareBound.flagRun (ShareJoint.shareCompJ adversary (q - 569))
                (ShareFinal.setupOf prfSeed publicSeed table)] :=
        ShareFinal.ex_comm _ _ _
    _ = ex ($ᵗ Digest : ProbComp Digest) fun publicSeed =>
          Pr[fun w => w.1.Good ∧ w.2.2.2 = true |
            ShareBound.flagGame publicSeed (ShareJoint.shareCompJ adversary (q - 569))] := by
        refine ex_congr _ fun publicSeed => ?_
        rw [ShareBound.flagGame, probEvent_eq_ex_bind]
        refine ex_congr _ fun prfSeed => ?_
        rw [probEvent_eq_ex_bind]
        refine ex_congr _ fun table => ?_
        rw [bind_pure_comp, probEvent_map]
        rfl
    _ ≤ ex ($ᵗ Digest : ProbComp Digest) fun _ =>
          (((q - 569 + ShareJoint.verifierAllowance + 231 : Nat) : ℝ≥0∞) /
            ((2 ^ 128 : Nat) : ℝ≥0∞)) :=
        ex_mono _ fun publicSeed => ShareBound.blind_bound_of publicSeed _ _
          fun setup hseed z hz => by
            have h := ShareJointBound.charged_blindRun_shareCompJ setup (hfiles setup) adversary
              (q - 569) z hz
            rwa [hseed] at h
    _ ≤ ((q - 569 + ShareJoint.verifierAllowance + 231 : Nat) : ℝ≥0∞) /
          ((2 ^ 128 : Nat) : ℝ≥0∞) :=
        ShareBound.ex_const_le _ _
    _ ≤ ((q - 8 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
        refine ENNReal.div_le_div_right (Nat.cast_le.mpr ?_) _
        unfold ShareJoint.verifierAllowance
        omega

end SlhDsaSecurity.ShareJointShared
