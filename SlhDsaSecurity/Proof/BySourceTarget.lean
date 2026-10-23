import SlhDsaSecurity.Proof.BySourceAnswer
import SlhDsaSecurity.Proof.BySourceShared

/-!
# `127` bits with every source counted but the signer

The three terms of the `127` proof, each at `BySourceBridge.TailBudget`:

* the answer half at `q / 2 ^ 128 + 2 ^ -126` (`answerBound`). The structural faults are charged
  per fresh entry and the target record per entry, and together they are within the
  adversary's work and the requests (`BySourceAnswer.fresh_add_right_le`), whatever the signer
  asks;
* the shared half at `(q - 512 + 259) / 2 ^ 128` (`BySourceShared.hshared`);
* the walk's own two coincidences.

They sum to at most `q / 2 ^ 127` exactly as at the total budget (`Target.allowanceAt`), and the
framework's hypotheses at `Security.allButSigner` give the tail budget
(`BySourceBridge.tailBudget_of`), so `HasLimitedSecurityBits .strong allButSigner 127`.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.BySourceTarget

open Security CanonicalGraph WarmedGame Target RoutedSplit BracketedRun CarrierTail CarrierThin
  FreshExpectation BySourceBridge BySourceAnswer

/-! ## The answer half -/

attribute [local irreducible] WarmedGame.afterSeeds Scheme.verify Scheme.keygenInternal
  Scheme.sign Security.signingOracle Security.countQueries

set_option maxHeartbeats 4000000 in
set_option linter.constructorNameAsVariable false in
open scoped Classical in
/-- **The answer half at `127`, the signer's calls free.** -/
theorem answerBound (q : Nat) (adversary : Adversary) (hbudget : TailBudget adversary q)
    (walk : Walk) (hwalk : walk ∈ support WarmedGame.graphWalk) (hgood : Target.GoodWalk walk) :
    Pr[fun result => RoutedSplit.AnswerBad ((walk.1, (FinalAssembly.forgetFused result).1),
          (FinalAssembly.forgetFused result).2) ∧ ¬ Target127.late (walk, result) |
        carrierTail keep127 adversary walk] ≤
      (q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / 2 ^ 126 := by
  classical
  by_cases hq : 2 ^ 128 ≤ q
  · refine le_trans probEvent_le_one (le_trans ?_ le_self_add)
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp)) (Or.inl (by simp)), one_mul]
    exact_mod_cast hq
  have hqlt : q < 2 ^ 128 := Nat.lt_of_not_le hq
  have hpublic : ¬ HashSeparation.Possible ((keyAt walk).seed, (keyAt walk).root) :=
    AnswerSide.not_possible_generatedKey hwalk hgood.2
  set split := SplitTail.splitCarrierTail (CombinedCharge.IsMessageInput (keyAt walk))
    QueryKind.hash QueryKind.verification keep127 adversary walk with hsplitDef
  have hmap : Prod.fst <$> split = carrierTail keep127 adversary walk :=
    SplitTail.map_splitCarrierTail _ AnswerFired.hash_ne_verification keep127 adversary walk
  have hmapR := SplitCarrierTail.forget_splitCarrierTail
    (CombinedCharge.IsMessageInput (keyAt walk)) QueryKind.hash QueryKind.verification keep127
    adversary walk
  have hfst : ∀ z ∈ support split, z.1 ∈ support (carrierTail keep127 adversary walk) := by
    intro z hz
    rw [← hmap, support_map]
    exact ⟨z, hz, rfl⟩
  have htailOf : ∀ result ∈ support (carrierTail keep127 adversary walk),
      FinalAssembly.forgetFused result ∈ support (WarmedGame.tail adversary walk) := by
    intro result hresult
    rw [← CarrierTail.forgetFused_carrierTail keep127 adversary walk, support_map]
    exact ⟨result, hresult, rfl⟩
  -- The two charges' counts, on every run, within the budget.
  have hpath : ∀ z ∈ support split,
      freshMass (Deviating walk) walk.2 z.1.2.1 + (z.1.2.2.2.length : ℝ≥0∞) ≤ (q : ℝ≥0∞) := by
    intro z hz
    refine le_trans (fresh_add_right_le adversary hwalk hgood z hz) ?_
    have h := (hbudget walk hwalk _ (htailOf z.1 (hfst z hz))).2
    exact_mod_cast (show z.1.1.1.1.counts.work + z.1.1.1.1.counts .signing ≤ q by
      simp only [FinalAssembly.forgetFused] at h
      omega)
  have hrightBound : ∀ result ∈ support (carrierTail keep127 adversary walk),
      result.2.2.2.length ≤ q := by
    intro result hresult
    rw [← hmap, support_map] at hresult
    obtain ⟨z, hz, rfl⟩ := hresult
    have h := le_trans le_add_self (hpath z hz)
    exact_mod_cast h
  have hleftBound := CarrierCap.leftRecord_le_cap_carrierTail keep127 adversary walk hpublic
    (fun keys hkeys => CarrierRecord.keys_publicKey keep127 walk hwalk keys hkeys)
    (fun result hresult => le_trans
      (SigningFaithful.signed_length_le_signing_tail adversary (htailOf result hresult))
      (hbudget walk hwalk _ (htailOf result hresult)).1)
  -- The event, at the split tail.
  have hevent : Pr[fun result => RoutedSplit.AnswerBad ((walk.1,
          (FinalAssembly.forgetFused result).1), (FinalAssembly.forgetFused result).2) ∧
          ¬ Target127.late (walk, result) | carrierTail keep127 adversary walk] =
      Pr[fun z : (((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState) × Counts =>
          RoutedSplit.AnswerBad ((walk.1, (FinalAssembly.forgetFused z.1).1),
            (FinalAssembly.forgetFused z.1).2) ∧ ¬ Target127.late (walk, z.1) | split] := by
    rw [← hmap, probEvent_map]
    rfl
  -- The structural faults, per fresh entry.
  have hbad : Pr[fun z : (((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState) × Counts =>
        GrowthCharge.Bad (AnswerSide.CanonicalBad walk.1.1.2.2 walk.1.2) (z.1.1, z.1.2.1) |
        split] ≤
      (∑' z, Pr[= z | split] * freshMass (Deviating walk) walk.2 z.1.2.1) *
        (1 / ((2 ^ 128 : Nat) : ℝ≥0∞)) := by
    have hprob : Pr[fun z : (((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState) ×
          Counts => GrowthCharge.Bad (AnswerSide.CanonicalBad walk.1.1.2.2 walk.1.2)
            (z.1.1, z.1.2.1) | split] =
        Pr[GrowthCharge.Bad (AnswerSide.CanonicalBad walk.1.1.2.2 walk.1.2) |
          (simulateQ KeygenUniform.rom (countQueries (ClassGrowth.splitCost
            (CombinedCharge.IsMessageInput (keyAt walk)) QueryKind.hash QueryKind.verification)
            (RecordedTail.recordedAfterSeeds adversary walk.1.1))).run walk.2] := by
      rw [← hmapR, probEvent_map]
      rfl
    rw [hprob]
    refine le_trans (prob_bad_le_expected_fresh (Deviating walk)
      (AnswerSide.CanonicalBad walk.1.1.2.2 walk.1.2) _
      (fun input => AnswerSide.prob_canonicalBad_le walk.1.1.2.2 walk.1.2 input)
      (fun input answer hbadness hnone => by
        unfold AnswerSide.CanonicalBad at hbadness
        rw [hnone] at hbadness
        cases hbadness)
      _ walk.2 (CanonicalTarget.clean_of_canonical_cache walk.1.1.2.2 walk.1.2 walk.2
        (WarmedCharges.walk_cache_canonical hwalk))) (le_of_eq ?_)
    rw [← hmapR, tsum_map_mul]
  -- The coverage, per target entry.
  have hcover : Pr[fun z : (((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState) ×
        Counts => AnswerFired.FiredCoveredRec walk z.1 | split] ≤
      (1 : ℝ≥0∞) / 2 ^ 126 +
        (∑' z, Pr[= z | split] * (z.1.2.2.2.length : ℝ≥0∞)) *
          (1 / ((2 ^ 128 : Nat) : ℝ≥0∞)) := by
    have hprob : Pr[fun z : (((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState) ×
          Counts => AnswerFired.FiredCoveredRec walk z.1 | split] =
        Pr[AnswerFired.FiredCoveredRec walk | carrierTail keep127 adversary walk] := by
      rw [← hmap, probEvent_map]
      rfl
    have hexpect : (∑' result, Pr[= result | carrierTail keep127 adversary walk] *
          ((result.2.2.2.length : Nat) : ℝ≥0∞)) =
        ∑' z, Pr[= z | split] * (z.1.2.2.2.length : ℝ≥0∞) := by
      rw [← hmap, tsum_map_mul]
    rw [hprob]
    refine le_trans (AnswerFired.prob_carrierTail_firedCovered_le adversary walk hwalk hgood
      (5 * 2 ^ 62) q le_rfl hleftBound hrightBound) (add_le_add le_rfl ?_)
    rw [hexpect]
    exact mul_le_mul' le_rfl (AnswerFired.second_order_fits q (by omega))
  have hsum : (∑' z, Pr[= z | split] * freshMass (Deviating walk) walk.2 z.1.2.1) +
        (∑' z, Pr[= z | split] * (z.1.2.2.2.length : ℝ≥0∞)) ≤ (q : ℝ≥0∞) := by
    rw [← ENNReal.tsum_add]
    simp_rw [← mul_add]
    exact tsum_mul_le_const split _ _ hpath
  rw [hevent]
  calc Pr[fun z : (((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState) × Counts =>
          RoutedSplit.AnswerBad ((walk.1, (FinalAssembly.forgetFused z.1).1),
            (FinalAssembly.forgetFused z.1).2) ∧ ¬ Target127.late (walk, z.1) | split]
      ≤ Pr[fun z : (((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState) × Counts =>
          GrowthCharge.Bad (AnswerSide.CanonicalBad walk.1.1.2.2 walk.1.2) (z.1.1, z.1.2.1) ∨
            AnswerFired.FiredCoveredRec walk z.1 | split] :=
        probEvent_mono fun z hz hev =>
          AnswerFired.join_carrierTail adversary walk hwalk hgood z.1 (hfst z hz) hev.1 hev.2
    _ ≤ _ := probEvent_or_le _ _ _
    _ ≤ (∑' z, Pr[= z | split] * freshMass (Deviating walk) walk.2 z.1.2.1) *
          (1 / ((2 ^ 128 : Nat) : ℝ≥0∞)) +
        ((1 : ℝ≥0∞) / 2 ^ 126 +
          (∑' z, Pr[= z | split] * (z.1.2.2.2.length : ℝ≥0∞)) *
            (1 / ((2 ^ 128 : Nat) : ℝ≥0∞))) := add_le_add hbad hcover
    _ = ((∑' z, Pr[= z | split] * freshMass (Deviating walk) walk.2 z.1.2.1) +
          (∑' z, Pr[= z | split] * (z.1.2.2.2.length : ℝ≥0∞))) *
            (1 / ((2 ^ 128 : Nat) : ℝ≥0∞)) + (1 : ℝ≥0∞) / 2 ^ 126 := by ring
    _ ≤ (q : ℝ≥0∞) * (1 / ((2 ^ 128 : Nat) : ℝ≥0∞)) + (1 : ℝ≥0∞) / 2 ^ 126 :=
        add_le_add (mul_le_mul' hsum le_rfl) le_rfl
    _ = (q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / 2 ^ 126 := by
        rw [div_eq_mul_one_div (q : ℝ≥0∞)]

/-! ## The shared half, at the refined paired run -/

/-- The shared half at the refined paired run. -/
theorem hsharedFused (q : Nat) (adversary : Adversary) (hbudget : TailBudget adversary q) :
    Pr[fun pair => GoodWalk pair.1 ∧
        (InputBad ((pair.1.1, (FinalAssembly.forgetFused pair.2).1),
          (FinalAssembly.forgetFused pair.2).2) ∨ Target127.late pair) |
      pairedFused (CarrierTail.carrierTail CarrierThin.keep127 adversary)] ≤
      ((q - 2 ^ subtreeHeight + 259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  have hpaired : pairedFused (CarrierTail.carrierTail CarrierThin.keep127 adversary) =
      LateProbes.pairedOf (CarrierTail.carrierTail CarrierThin.keep127) adversary := rfl
  rw [hpaired]
  refine le_trans (le_of_eq ?_) (BySourceShared.hshared q adversary hbudget)
  exact LateProbes.probEvent_forget (CarrierTail.forgetsTo CarrierThin.keep127 adversary)
    (fun pair : SharedJoin.RecordedPair => GoodWalk pair.1 ∧
      (InputBad (SharedJoin.recordedTraceOf pair) ∨ Target127.Late pair))

/-! ## The win, as the three terms -/

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 2000000 in
/-- **The tail budget bounds the win by the three terms.** -/
theorem warmed_le (q : Nat) (adversary : Adversary) (hbudget : TailBudget adversary q) :
    Pr[fun result => Wins .strong result.1.2.1 | WarmedGame.warmedRun adversary] ≤
      ((q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / 2 ^ 126) +
        (((q - 2 ^ subtreeHeight + 259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
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
        (answerBound q adversary hbudget walk hwalk hgood)
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
          (((q - 2 ^ subtreeHeight + 259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
            (1 / ((2 ^ 128 : Nat) : ℝ≥0∞) + 1 / ((2 ^ 165 : Nat) : ℝ≥0∞))) :=
        add_le_add hgoodAnswer
          (add_le_add (hsharedFused q adversary hbudget)
            (prob_bad_walk_pairedFused (CarrierTail.carrierTail CarrierThin.keep127 adversary)))

/-! ## `127`, every source counted but the signer -/

set_option maxHeartbeats 1000000 in
/-- **The win at the warmed run, within `q / 2 ^ 127`.** -/
theorem warmed_bound (q : Nat) (adversary : Adversary) (hbudget : TailBudget adversary q) :
    Pr[fun result => Wins .strong result.1.2.1 | WarmedGame.warmedRun adversary] ≤
      (q : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
  have hkeygen := BySourceShared.keygen_le_of_tail hbudget
  have hkn : (chains + 1) * 2 ^ subtreeHeight = 18432 := by decide
  have h2 : 2 ^ subtreeHeight = 512 := by decide
  rw [hkn] at hkeygen
  refine le_trans (warmed_le q adversary hbudget) ?_
  calc _ = ((q - 2 ^ subtreeHeight + 259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
          ((q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + defectsAt ((1 : ℝ≥0∞) / 2 ^ 126)) := by
        unfold defectsAt
        ring
    _ ≤ (q : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) :=
        allowanceAt _ 259 6 q AnswerFired.defects_le (by decide)
          (by rw [h2]; clear * - hkeygen; omega)

/-- **`SLH-DSA-SHAKE-128s` has `127` bits of strong security with every source counted but the
signer**: requests, the adversary's own hash calls, key generation's and final verification's. -/
theorem hasLimitedSecurityBits_strong_127 : HasLimitedSecurityBits .strong allButSigner 127 := by
  intro q _ adversary hlimit hbound
  rw [advantage_securityGame, totalAdvantage,
    MainTheorem.probEvent_runAll adversary (fun result => Wins .strong result.1),
    WarmedGame.probEvent_warmed adversary (fun outcome => Wins .strong outcome.1)]
  exact warmed_bound q adversary (tailBudget_of .strong hlimit hbound)

/-- The game's counts do not depend on the notion. -/
theorem probEvent_counts (notion : Notion) (adversary : Adversary)
    (event : Xmss.Unforgeability.QueryCounts → Prop) :
    Pr[fun result => event result.2 | (securityGame notion).experiment () adversary] =
      Pr[fun result => event result.2 | runBySource adversary] := by
  change Pr[fun result => event result.2 |
    (fun result => (decide (Wins notion result.1), result.2)) <$> runBySource adversary] = _
  rw [probEvent_map]
  rfl

/-- **And of standard security**, a standard forgery being a strong one. -/
theorem hasLimitedSecurityBits_standard_127 :
    HasLimitedSecurityBits .standard allButSigner 127 := by
  intro q hq adversary hlimit hbound
  have hlimit' : WithinSigningLimit .strong adversary :=
    (probEvent_counts .strong adversary (fun counts => counts .sign ≤ signingLimit)).trans
      ((probEvent_counts .standard adversary (fun counts => counts .sign ≤ signingLimit)).symm.trans
        hlimit)
  have hbound' : (securityGame .strong).HasQueryBound () allButSigner adversary q :=
    (probEvent_counts .strong adversary
        (fun counts => ∑ kind ∈ allButSigner, counts kind ≤ q)).trans
      ((probEvent_counts .standard adversary
        (fun counts => ∑ kind ∈ allButSigner, counts kind ≤ q)).symm.trans hbound)
  rw [advantage_securityGame]
  refine (totalAdvantage_standard_le_strong adversary).trans ?_
  have h := hasLimitedSecurityBits_strong_127 q hq adversary hlimit' hbound'
  rwa [advantage_securityGame] at h

end SlhDsaSecurity.BySourceTarget
