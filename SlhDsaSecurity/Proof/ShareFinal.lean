import SlhDsaSecurity.Proof.ShareEvent
import SlhDsaSecurity.Proof.AnswerFired
import SlhDsaSecurity.Proof.RecordedWalkTable

/-!
# The shared half at `127`, and the statement

At one setup the chain is: the real game has the law of the capped real game (the budget keeps
the cap from firing, `ShareRealCap`); the capped real game is coupled with the lenient game so
that the event raises the lenient flag (`ShareWhole`, `ShareEvent`); the lenient flag has the law
of the blind flag (`ShareUntilBad`). Averaged over `SK.prf`, the public seed and the table, the
blind flag off a bad walk is at most `(L + 3929 + 259) / 2 ^ 128` (`ShareBound.blind_bound`) with
`L = q - (chains + 1) · 2 ^ subtreeHeight`, which is at most `(q - 512 + 259) / 2 ^ 128`. That
is `AnswerFired.target_of_shared`'s hypothesis, and with it `HasTotalSecurityBits .strong 127`.
-/

open OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational

namespace SlhDsaSecurity.ShareFinal

open Security CanonicalGraph ShareGame ShareCouple ShareInv ShareWhole ShareEvent

/-! ## At one setup -/

/-- The real event at a setup, on the flattened real game's output. -/
def RealEvent (setup : Setup)
    (real : (((Forgery × Multiplicative RecordedQueries.Tally) × (Bool × RecordedQueries.Tally)) ×
      SigningLog) × QueryCache HashSpec) : Prop :=
  RoutedSplit.InputBad (SharedJoin.recordedTraceOf (realPair setup real)) ∨
    Target127.Late (realPair setup real)

set_option maxHeartbeats 2000000 in
/-- **At a good setup, the real event is at most the blind flag**, provided the real phase stays
within the cap. -/
theorem setup_bound (setup : Setup) (hgood : setup.Good) (adversary : Adversary) (limit : Nat)
    (hbound : ∀ z ∈ support ((simulateQ (SharePresent.realImpl
        (StrippedGame.strippedSign setup.warm setup.sk)) (adversary.main setup.pk)).run
          (1, [], setup.warm)), ShareRealCap.realCost z.2 ≤ limit) :
    Pr[RealEvent setup | SharePresent.realFlat adversary (setup.sk, setup.pk) setup.warm] ≤
      Pr[fun z => z.2.2 = true | ShareBound.flagRun adversary limit setup] := by
  rw [← probEvent_congr' (fun _ _ => Iff.rfl)
    (ShareRealCap.evalDist_realFlat_cap adversary (setup.sk, setup.pk) setup.warm limit hbound)]
  refine le_trans (probEvent_le_of_relTriple_imp (Q := fun lenient => lenient.2.2 = true)
    (relTriple_support_left (couple_whole setup hgood adversary limit)) ?_) ?_
  · rintro real lenient ⟨hfinal, hreal⟩ hevent
    obtain ⟨hforgery, stateV, hinv, hclaims, hcache, hlog, hadv, hver⟩ := hfinal
    rw [hclaims, hforgery]
    cases hflag : stateV.2 with
    | true => simp [claimsStep, hflag]
    | false =>
      rcases hevent with hbad | hlate | hlate
      · exact flag_of_inputBad setup hgood adversary limit real hreal stateV hinv hflag hcache hlog
          hver hbad
      · have := flag_of_prfHit setup real stateV hinv hadv hver hlate
        rw [hflag] at this
        cases this
      · have := flag_of_signerHit setup hgood real stateV hinv hcache hlog hlate
        rw [hflag] at this
        cases this
  · exact le_of_eq (ShareUntilBad.probEvent_bad_eq setup _ St.start)

/-! ## The budget pays for key generation -/

attribute [local irreducible] WarmedGame.afterSeeds Scheme.verify Scheme.keygenInternal
  Security.countQueries

set_option maxHeartbeats 1000000 in
/-- **A budget is at least what key generation spends**, in full. -/
theorem keygen_le_of_budget {adversary : Adversary} {q : Nat} (hbudget : HasTotalBudget adversary q) :
    (chains + 1) * 2 ^ subtreeHeight ≤ q := by
  let table : Cells × Padding := default
  let walk := WalkTable.walkOfTable default default table
  obtain ⟨result, hresult⟩ := CapComp.exists_mem_support
    (WarmedGame.tail adversary walk) probFailure_eq_zero
  have htotal := WarmedCharges.count_le_of_budget_tail hbudget
    (WalkTable.mem_support_graphWalk_walkOfTable default default table) hresult
  obtain ⟨keygenCount, keys, keyCache, hkeys, hsum⟩ :=
    AdversaryQueries.work_add_keygen_add_served_le_total adversary walk.1.1 walk.2 result hresult
  have hkeygen := KeygenCost.count_keygen_ge _ _ _ _ _ hkeys
  simp only at hkeygen
  omega

/-! ## At one walk -/

/-- The cap the shared half runs the adversary at. -/
def capLimit (q : Nat) : Nat := q - (chains + 1) * 2 ^ subtreeHeight

/-- The setup a drawn walk is. -/
def setupOf (prfSeed publicSeed : Digest) (table : Cells × Padding) : Setup :=
  ⟨prfSeed, publicSeed, table⟩

theorem goodWalk_iff (prfSeed publicSeed : Digest) (table : Cells × Padding) :
    Target.GoodWalk (WalkTable.walkOfTable prfSeed publicSeed table) ↔
      (setupOf prfSeed publicSeed table).Good := Iff.rfl

set_option maxHeartbeats 4000000 in
/-- **At one walk, the shared event is at most the blind flag off a bad walk.** -/
theorem walk_bound {adversary : Adversary} {q : Nat} (hbudget : HasTotalBudget adversary q)
    (prfSeed publicSeed : Digest) (table : Cells × Padding) :
    Pr[fun result => Target.GoodWalk (WalkTable.walkOfTable prfSeed publicSeed table) ∧
        (RoutedSplit.InputBad (SharedJoin.recordedTraceOf
            (WalkTable.walkOfTable prfSeed publicSeed table, result)) ∨
          Target127.Late (WalkTable.walkOfTable prfSeed publicSeed table, result)) |
      RecordedTail.recordedTail adversary (WalkTable.walkOfTable prfSeed publicSeed table)] ≤
      Pr[fun z => (setupOf prfSeed publicSeed table).Good ∧ z.2.2 = true |
        ShareBound.flagRun adversary (capLimit q) (setupOf prfSeed publicSeed table)] := by
  classical
  by_cases hgood : (setupOf prfSeed publicSeed table).Good
  · refine le_trans (probEvent_mono fun result _ hevent => hevent.2) ?_
    have hlinked := SharePresent.probEvent_recordedTail_linked adversary prfSeed publicSeed table
      (fun x => RoutedSplit.InputBad (SharedJoin.recordedTraceOf
          (WalkTable.walkOfTable prfSeed publicSeed table, ((x.1, 0), x.2))) ∨
        Target127.Late (WalkTable.walkOfTable prfSeed publicSeed table, ((x.1, 0), x.2)))
    refine le_trans (le_of_eq hlinked) ?_
    rw [SharePresent.linkedRun_eq, TouchedKeys.keysOf_eq]
    refine le_trans (setup_bound (setupOf prfSeed publicSeed table) hgood adversary (capLimit q)
      ?_) (probEvent_mono fun z _ hz => ⟨hgood, hz⟩)
    intro z hz
    have h := ShareRealCap.cost_le_of_budget hbudget prfSeed publicSeed table z
    rw [TouchedKeys.keysOf_eq] at h
    exact h hz
  · refine le_trans (le_of_eq (probEvent_eq_zero fun result _ hevent =>
      hgood ((goodWalk_iff prfSeed publicSeed table).mp hevent.1))) (by simp)

/-! ## Averaged over the seeds and the table -/

open BlindCharge in
theorem ex_comm {α β : Type} (mx : ProbComp α) (my : ProbComp β) (f : α → β → ℝ≥0∞) :
    ex mx (fun a => ex my (f a)) = ex my (fun b => ex mx (fun a => f a b)) := by
  unfold ex
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun b => tsum_congr fun a => ?_
  ring

open BlindCharge in
set_option maxHeartbeats 4000000 in
/-- **The shared half's obligation at `127`.** -/
theorem hshared (q : Nat) (adversary : Adversary) (hbudget : HasTotalBudget adversary q) :
    Pr[fun pair : SharedJoin.RecordedPair => Target.GoodWalk pair.1 ∧
        (RoutedSplit.InputBad (SharedJoin.recordedTraceOf pair) ∨ Target127.Late pair) |
      RandomiserRecord.recordedPairedRun adversary] ≤
      ((q - 2 ^ subtreeHeight + 259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  have hq := keygen_le_of_budget hbudget
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (RecordedWalkTable.evalDist_recordedPairedRun adversary)]
  calc Pr[fun pair : SharedJoin.RecordedPair => Target.GoodWalk pair.1 ∧
          (RoutedSplit.InputBad (SharedJoin.recordedTraceOf pair) ∨ Target127.Late pair) |
        (do
          let prfSeed ← ($ᵗ Digest : ProbComp Digest)
          let publicSeed ← ($ᵗ Digest : ProbComp Digest)
          RecordedWalkTable.recordedTableRun adversary prfSeed publicSeed)]
      = ex ($ᵗ Digest : ProbComp Digest) fun prfSeed => ex ($ᵗ Digest : ProbComp Digest)
          fun publicSeed => ex ($ᵗ (Cells × Padding) : ProbComp (Cells × Padding)) fun table =>
            Pr[fun result => Target.GoodWalk (WalkTable.walkOfTable prfSeed publicSeed table) ∧
                (RoutedSplit.InputBad (SharedJoin.recordedTraceOf
                    (WalkTable.walkOfTable prfSeed publicSeed table, result)) ∨
                  Target127.Late (WalkTable.walkOfTable prfSeed publicSeed table, result)) |
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
            Pr[fun z => (setupOf prfSeed publicSeed table).Good ∧ z.2.2 = true |
              ShareBound.flagRun adversary (capLimit q) (setupOf prfSeed publicSeed table)] :=
        ex_mono _ fun prfSeed => ex_mono _ fun publicSeed => ex_mono _ fun table =>
          walk_bound hbudget prfSeed publicSeed table
    _ = ex ($ᵗ Digest : ProbComp Digest) fun publicSeed => ex ($ᵗ Digest : ProbComp Digest)
          fun prfSeed => ex ($ᵗ (Cells × Padding) : ProbComp (Cells × Padding)) fun table =>
            Pr[fun z => (setupOf prfSeed publicSeed table).Good ∧ z.2.2 = true |
              ShareBound.flagRun adversary (capLimit q) (setupOf prfSeed publicSeed table)] :=
        ex_comm _ _ _
    _ = ex ($ᵗ Digest : ProbComp Digest) fun publicSeed =>
          Pr[fun w => w.1.Good ∧ w.2.2.2 = true |
            ShareBound.flagGame publicSeed adversary (capLimit q)] := by
        refine ex_congr _ fun publicSeed => ?_
        rw [ShareBound.flagGame, probEvent_eq_ex_bind]
        refine ex_congr _ fun prfSeed => ?_
        rw [probEvent_eq_ex_bind]
        refine ex_congr _ fun table => ?_
        rw [bind_pure_comp, probEvent_map]
        rfl
    _ ≤ ex ($ᵗ Digest : ProbComp Digest) fun _ =>
          ((capLimit q + 3929 + 259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) :=
        ex_mono _ fun publicSeed => ShareBound.blind_bound publicSeed adversary (capLimit q)
    _ ≤ ((capLimit q + 3929 + 259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) :=
        ShareBound.ex_const_le _ _
    _ ≤ ((q - 2 ^ subtreeHeight + 259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
        refine ENNReal.div_le_div_right (Nat.cast_le.mpr ?_) _
        unfold capLimit
        have : (chains + 1) * 2 ^ subtreeHeight = 18432 := by decide
        have h2 : 2 ^ subtreeHeight = 512 := by decide
        rw [this] at hq ⊢
        rw [h2]
        omega

/-- **`SLH-DSA-SHAKE-128s` has `127` bits of total strong security.** -/
theorem hasTotalSecurityBits_strong_127 : HasTotalSecurityBits .strong 127 :=
  AnswerFired.target_of_shared hshared

end SlhDsaSecurity.ShareFinal
