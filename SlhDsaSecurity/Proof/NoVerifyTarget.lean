import SlhDsaSecurity.Proof.NoVerifyBudget

/-!
# `127` bits with final verification's calls uncharged

The `127` proof at `HasTotalBudget` is a sum of three terms: the answer half at `q`, the shared
half at `q - (chains + 1) · 2 ^ subtreeHeight + 3929 + 259`, and the walk's own coincidences.
A `HasNoVerifyBudget` adversary at `q` is a `HasTotalBudget` one at `q + 3824`
(`NoVerifyBudget.hasTotalBudget_of_noVerify`); at that budget the answer half grows by `3824`,
and the shared half still has key generation's `36 · 512` minus the verifier's `3929` and the
claims' `259` in hand, which pays for it with room to spare. So the uncharged verifier costs
nothing at `127`.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.NoVerifyTarget

open Security CanonicalGraph ShareGame ShareCouple ShareInv ShareWhole ShareEvent ShareFinal
  WarmedGame Target RoutedSplit

/-! ## The shared half at its own constant -/

open BlindCharge in
set_option maxHeartbeats 4000000 in
/-- **The shared half, before the final weakening**: the cap, the verifier and the claims. -/
theorem hsharedCore (q : Nat) (adversary : Adversary) (hbudget : HasTotalBudget adversary q) :
    Pr[fun pair : SharedJoin.RecordedPair => Target.GoodWalk pair.1 ∧
        (RoutedSplit.InputBad (SharedJoin.recordedTraceOf pair) ∨ Target127.Late pair) |
      RandomiserRecord.recordedPairedRun adversary] ≤
      ((ShareFinal.capLimit q + 3929 + 259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
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


/-- The shared half at the refined paired run. -/
theorem hsharedFused (q : Nat) (adversary : Adversary) (hbudget : HasTotalBudget adversary q) :
    Pr[fun pair => GoodWalk pair.1 ∧
        (InputBad ((pair.1.1, (FinalAssembly.forgetFused pair.2).1),
          (FinalAssembly.forgetFused pair.2).2) ∨ Target127.late pair) |
      pairedFused (CarrierTail.carrierTail CarrierThin.keep127 adversary)] ≤
      ((ShareFinal.capLimit q + 3929 + 259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  have hpaired : pairedFused (CarrierTail.carrierTail CarrierThin.keep127 adversary) =
      LateProbes.pairedOf (CarrierTail.carrierTail CarrierThin.keep127) adversary := rfl
  rw [hpaired]
  refine le_trans (le_of_eq ?_) (hsharedCore q adversary hbudget)
  exact LateProbes.probEvent_forget (CarrierTail.forgetsTo CarrierThin.keep127 adversary)
    (fun pair : SharedJoin.RecordedPair => GoodWalk pair.1 ∧
      (InputBad (SharedJoin.recordedTraceOf pair) ∨ Target127.Late pair))

/-! ## The win, as the three terms -/

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 2000000 in
/-- **A total budget bounds the win by the three terms**, the shared one at its own constant. -/
theorem warmed_le (q : Nat) (adversary : Adversary) (hbudget : HasTotalBudget adversary q) :
    Pr[fun result => Wins .strong result.1.2.1 | WarmedGame.warmedRun adversary] ≤
      ((q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / 2 ^ 126) +
        (((ShareFinal.capLimit q + 3929 + 259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
          (1 / ((2 ^ 128 : Nat) : ℝ≥0∞) + 1 / ((2 ^ 165 : Nat) : ℝ≥0∞))) := by
  classical
  rw [WarmedGame.warmedRun_eq, probEvent_map,
    show (do let walk ← graphWalk; let result ← tail adversary walk; pure (walk, result)) =
      pairedRun adversary from rfl,
    pairedRun_eq_map_pairedFused adversary (CarrierTail.carrierTail CarrierThin.keep127 adversary) FinalAssembly.forgetFused (CarrierTail.forgetFused_carrierTail CarrierThin.keep127 adversary),
    probEvent_map]
  have hgoodAnswer :
      Pr[fun pair => GoodWalk pair.1 ∧
          AnswerBad ((pair.1.1, (FinalAssembly.forgetFused pair.2).1), (FinalAssembly.forgetFused pair.2).2) ∧ ¬ Target127.late pair |
        pairedFused (CarrierTail.carrierTail CarrierThin.keep127 adversary)] ≤
        (q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / 2 ^ 126 := by
    refine Averaging.probEvent_bind_pair_le graphWalk (CarrierTail.carrierTail CarrierThin.keep127 adversary)
      (fun walk result => GoodWalk walk ∧
        AnswerBad ((walk.1, (FinalAssembly.forgetFused result).1), (FinalAssembly.forgetFused result).2) ∧ ¬ Target127.late (walk, result)) _
      fun walk hwalk => ?_
    by_cases hgood : GoodWalk walk
    · exact le_trans (probEvent_mono fun result _ hbad => hbad.2)
        (AnswerFired.answerBound127 q adversary hbudget walk hwalk hgood)
    · rw [show (fun result => GoodWalk walk ∧
        AnswerBad ((walk.1, (FinalAssembly.forgetFused result).1), (FinalAssembly.forgetFused result).2) ∧
          ¬ Target127.late (walk, result)) = fun _ => False from by funext _; simp [hgood]]
      simp
  calc Pr[fun pair => Wins .strong (FinalAssembly.forgetFused pair.2).1.1 | pairedFused (CarrierTail.carrierTail CarrierThin.keep127 adversary)]
      ≤ Pr[fun pair => (GoodWalk pair.1 ∧
            AnswerBad ((pair.1.1, (FinalAssembly.forgetFused pair.2).1), (FinalAssembly.forgetFused pair.2).2) ∧ ¬ Target127.late pair) ∨
          ((GoodWalk pair.1 ∧
            (InputBad ((pair.1.1, (FinalAssembly.forgetFused pair.2).1), (FinalAssembly.forgetFused pair.2).2) ∨ Target127.late pair)) ∨
              ¬ GoodWalk pair.1) | pairedFused (CarrierTail.carrierTail CarrierThin.keep127 adversary)] := by
        refine probEvent_mono fun pair hpair hwin => ?_
        by_cases hgood : GoodWalk pair.1
        · obtain ⟨walk, hwalk, result, hresult, hpair⟩ : ∃ walk ∈ support graphWalk,
              ∃ result ∈ support (CarrierTail.carrierTail CarrierThin.keep127 adversary walk), (walk, result) = pair := by
            simpa [pairedFused, eq_comm] using hpair
          subst hpair
          have hforgetMem : FinalAssembly.forgetFused result ∈ support (tail adversary walk) := by
            rw [← CarrierTail.forgetFused_carrierTail CarrierThin.keep127 adversary walk, support_map]
            exact ⟨result, hresult, rfl⟩
          by_cases hlate : Target127.late (walk, result)
          · exact Or.inr (Or.inl ⟨hgood, Or.inr hlate⟩)
          · rcases SigningFaithful.cases_of_win_charged adversary hwalk hforgetMem hwin with
              hAnswerBad | hInputBad
            · exact Or.inl ⟨hgood, hAnswerBad, hlate⟩
            · exact Or.inr (Or.inl ⟨hgood, Or.inl hInputBad⟩)
        · exact Or.inr (Or.inr hgood)
    _ ≤ Pr[fun pair => GoodWalk pair.1 ∧
            AnswerBad ((pair.1.1, (FinalAssembly.forgetFused pair.2).1), (FinalAssembly.forgetFused pair.2).2) ∧ ¬ Target127.late pair |
            pairedFused (CarrierTail.carrierTail CarrierThin.keep127 adversary)] +
          Pr[fun pair => (GoodWalk pair.1 ∧
            (InputBad ((pair.1.1, (FinalAssembly.forgetFused pair.2).1), (FinalAssembly.forgetFused pair.2).2) ∨ Target127.late pair)) ∨
              ¬ GoodWalk pair.1 | pairedFused (CarrierTail.carrierTail CarrierThin.keep127 adversary)] := probEvent_or_le _ _ _
    _ ≤ Pr[fun pair => GoodWalk pair.1 ∧
            AnswerBad ((pair.1.1, (FinalAssembly.forgetFused pair.2).1), (FinalAssembly.forgetFused pair.2).2) ∧ ¬ Target127.late pair |
            pairedFused (CarrierTail.carrierTail CarrierThin.keep127 adversary)] +
          (Pr[fun pair => GoodWalk pair.1 ∧
              (InputBad ((pair.1.1, (FinalAssembly.forgetFused pair.2).1), (FinalAssembly.forgetFused pair.2).2) ∨ Target127.late pair) |
              pairedFused (CarrierTail.carrierTail CarrierThin.keep127 adversary)] +
            Pr[fun pair => ¬ GoodWalk pair.1 | pairedFused (CarrierTail.carrierTail CarrierThin.keep127 adversary)]) :=
        add_le_add le_rfl (probEvent_or_le _ _ _)
    _ ≤ ((q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / 2 ^ 126) +
          (((ShareFinal.capLimit q + 3929 + 259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
            (1 / ((2 ^ 128 : Nat) : ℝ≥0∞) + 1 / ((2 ^ 165 : Nat) : ℝ≥0∞))) :=
        add_le_add hgoodAnswer
          (add_le_add (hsharedFused q adversary hbudget)
            (prob_bad_walk_pairedFused (CarrierTail.carrierTail CarrierThin.keep127 adversary)))

/-! ## `127` with verification uncharged -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
/-- **`SLH-DSA-SHAKE-128s` has `127` bits of strong security with every hash call charged except
final verification's.** The budget at `q` is a total budget at `q + 3824`. The answer half pays the
extra `3824` units at face value; the shared half's own constant is `capLimit` less what key
generation reserved, and key generation's `18432` calls leave room for the extra `3824` there too. -/
theorem hasNoVerifySecurityBits_strong_127 : HasNoVerifySecurityBits .strong 127 := by
  intro q _ adversary hbudget
  have htotal := NoVerifyBudget.hasTotalBudget_of_noVerify hbudget
  have hkeygen := ShareFinal.keygen_le_of_budget htotal
  have hkn : (chains + 1) * 2 ^ subtreeHeight = 18432 := by decide
  have h2 : 2 ^ subtreeHeight = 512 := by decide
  rw [hkn] at hkeygen
  rw [totalAdvantage, MainTheorem.probEvent_runAll adversary (fun result => Wins .strong result.1),
    WarmedGame.probEvent_warmed adversary (fun outcome => Wins .strong outcome.1)]
  refine le_trans (warmed_le (q + 3824) adversary htotal) ?_
  have hnum : (q + 3824) + (ShareFinal.capLimit (q + 3824) + 3929 + 259) ≤
      (q - 2 ^ subtreeHeight + 259) + q := by
    unfold ShareFinal.capLimit
    rw [hkn, h2]
    clear * - hkeygen
    omega
  have hcast : ((q + 3824 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
        ((ShareFinal.capLimit (q + 3824) + 3929 + 259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) ≤
      ((q - 2 ^ subtreeHeight + 259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
        (q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
    rw [ENNReal.div_add_div_same, ENNReal.div_add_div_same, ← Nat.cast_add, ← Nat.cast_add]
    exact ENNReal.div_le_div_right (Nat.cast_le.mpr hnum) _
  calc _ = (((q + 3824 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
          ((ShareFinal.capLimit (q + 3824) + 3929 + 259 : Nat) : ℝ≥0∞) /
            ((2 ^ 128 : Nat) : ℝ≥0∞)) + defectsAt ((1 : ℝ≥0∞) / 2 ^ 126) := by
        unfold defectsAt
        ring
    _ ≤ (((q - 2 ^ subtreeHeight + 259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
          (q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)) + defectsAt ((1 : ℝ≥0∞) / 2 ^ 126) :=
        add_le_add hcast le_rfl
    _ = ((q - 2 ^ subtreeHeight + 259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
          ((q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + defectsAt ((1 : ℝ≥0∞) / 2 ^ 126)) :=
        add_assoc _ _ _
    _ ≤ (q : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) :=
        allowanceAt _ 259 6 q AnswerFired.defects_le (by decide) (by rw [h2]; clear * - hkeygen; omega)

/-- A standard forgery is a strong one, so the bound carries over. -/
theorem hasNoVerifySecurityBits_standard_127 : HasNoVerifySecurityBits .standard 127 := by
  intro q hq adversary hbudget
  exact (totalAdvantage_standard_le_strong adversary).trans
    (hasNoVerifySecurityBits_strong_127 q hq adversary hbudget)

end SlhDsaSecurity.NoVerifyTarget
