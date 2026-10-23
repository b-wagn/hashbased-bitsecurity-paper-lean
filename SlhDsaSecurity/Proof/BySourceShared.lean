import SlhDsaSecurity.Proof.ShareFinal
import SlhDsaSecurity.Proof.BySourceBridge

/-!
# The shared half, with the signer's calls free

`ShareFinal.hshared` reads the budget in two places, and neither needs the signer's calls. The
cap `L = q - (chains + 1) · 2 ^ subtreeHeight` is a cap on the adversary's own calls plus one per
served request, and `ShareRealCap.cost_le_of_budget` pays for it out of the total count by
noting that key generation spends its top tree and each served request costs the signer two
calls. With the requests counted directly, the second half of that is not needed: a served
request is a request, and requests are in the budget. So `cost_le_of_tail` reads the same cap
off `BySourceBridge.TailBudget`, and the rest of the half is `ShareFinal`'s, line for line.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.BySourceShared

open Security CanonicalGraph WarmedGame WalkTable TableTail RecordedQueries RecordedPhase
  SharePresent ShareRealCap BySourceBridge

attribute [local irreducible] WarmedGame.afterSeeds Scheme.verify Scheme.keygenInternal
  Security.countQueries

theorem servedCount_le_length (log : SigningLog) :
    AdversaryQueries.servedCount log ≤ log.length :=
  List.length_filter_le _ _

set_option maxHeartbeats 2000000 in
/-- **On every path of the real phase, the cap's weight is within the budget left after key
generation**, the signer's calls uncounted. -/
theorem cost_le_of_tail {adversary : Adversary} {q : Nat} (hbudget : TailBudget adversary q)
    (prfSeed publicSeed : Digest) (table : Cells × Padding) :
    ∀ z ∈ support ((simulateQ (realImpl (StrippedGame.strippedSign
        (walkOfTable prfSeed publicSeed table).2 (keysOf prfSeed publicSeed table).1))
        (adversary.main (keysOf prfSeed publicSeed table).2)).run
          (1, [], (walkOfTable prfSeed publicSeed table).2)),
      realCost z.2 ≤ q - (chains + 1) * 2 ^ subtreeHeight := by
  intro z hz
  obtain ⟨w, hw⟩ := CapComp.exists_mem_support _ (CapComp.run_neverFails realWorldImpl
    (fun _ _ => probFailure_eq_zero)
    (Scheme.verify (keysOf prfSeed publicSeed table).2 z.1.message z.1.signature) (1, z.2.2.2))
  have hr : ((((z.1, z.2.1), (w.1, Multiplicative.toAdd w.2.1)), z.2.2.1), w.2.2) ∈
      support (linkedRun adversary prfSeed publicSeed table) := by
    rw [linkedRun_eq, realFlat, mem_support_bind_iff]
    refine ⟨z, hz, ?_⟩
    rw [mem_support_bind_iff]
    exact ⟨w, hw, by simp⟩
  obtain ⟨result, hresult, houtcome, -⟩ :=
    exists_recordedTail_of_linked adversary prfSeed publicSeed table _ hr
  have htail : ((result.1.1.1, result.1.2), result.2) ∈
      support (WarmedGame.tail adversary (walkOfTable prfSeed publicSeed table)) := by
    rw [RecordedTail.tail_eq_map_recordedTail, support_map]
    exact ⟨result, hresult, rfl⟩
  have htotal := hbudget _ (mem_support_graphWalk_walkOfTable prfSeed publicSeed table) _ htail
  have hlength := SigningFaithful.signed_length_le_signing_tail adversary htail
  have hcounts : result.1.1.1.counts =
      (Multiplicative.toAdd z.2.1).1 + (Multiplicative.toAdd w.2.1).1 := by
    rw [houtcome]
    rfl
  have hsigned : result.1.1.1.signed = z.2.2.1 := by
    rw [houtcome]
    rfl
  have hserved := servedCount_le_length z.2.2.1
  simp only [hcounts, hsigned, AdversaryQueries.work_add] at htotal hlength
  simp only [Pi.add_apply] at htotal hlength
  unfold realCost
  omega

set_option maxHeartbeats 1000000 in
/-- **A budget is at least what key generation spends**, in full. -/
theorem keygen_le_of_tail {adversary : Adversary} {q : Nat} (hbudget : TailBudget adversary q) :
    (chains + 1) * 2 ^ subtreeHeight ≤ q := by
  let table : Cells × Padding := default
  let walk := WalkTable.walkOfTable default default table
  obtain ⟨result, hresult⟩ := CapComp.exists_mem_support
    (WarmedGame.tail adversary walk) probFailure_eq_zero
  have h := (hbudget walk
    (WalkTable.mem_support_graphWalk_walkOfTable default default table) result hresult).2
  omega

set_option maxHeartbeats 4000000 in
/-- **At one walk, the shared event is at most the blind flag off a bad walk.** -/
theorem walk_bound {adversary : Adversary} {q : Nat} (hbudget : TailBudget adversary q)
    (prfSeed publicSeed : Digest) (table : Cells × Padding) :
    Pr[fun result => Target.GoodWalk (WalkTable.walkOfTable prfSeed publicSeed table) ∧
        (RoutedSplit.InputBad (SharedJoin.recordedTraceOf
            (WalkTable.walkOfTable prfSeed publicSeed table, result)) ∨
          Target127.Late (WalkTable.walkOfTable prfSeed publicSeed table, result)) |
      RecordedTail.recordedTail adversary (WalkTable.walkOfTable prfSeed publicSeed table)] ≤
      Pr[fun z => (ShareFinal.setupOf prfSeed publicSeed table).Good ∧ z.2.2 = true |
        ShareBound.flagRun adversary (ShareFinal.capLimit q)
          (ShareFinal.setupOf prfSeed publicSeed table)] := by
  classical
  by_cases hgood : (ShareFinal.setupOf prfSeed publicSeed table).Good
  · refine le_trans (probEvent_mono fun result _ hevent => hevent.2) ?_
    have hlinked := SharePresent.probEvent_recordedTail_linked adversary prfSeed publicSeed table
      (fun x => RoutedSplit.InputBad (SharedJoin.recordedTraceOf
          (WalkTable.walkOfTable prfSeed publicSeed table, ((x.1, 0), x.2))) ∨
        Target127.Late (WalkTable.walkOfTable prfSeed publicSeed table, ((x.1, 0), x.2)))
    refine le_trans (le_of_eq hlinked) ?_
    rw [SharePresent.linkedRun_eq, TouchedKeys.keysOf_eq]
    refine le_trans (ShareFinal.setup_bound (ShareFinal.setupOf prfSeed publicSeed table) hgood
      adversary (ShareFinal.capLimit q) ?_) (probEvent_mono fun z _ hz => ⟨hgood, hz⟩)
    intro z hz
    have h := cost_le_of_tail hbudget prfSeed publicSeed table z
    rw [TouchedKeys.keysOf_eq] at h
    exact h hz
  · refine le_trans (le_of_eq (probEvent_eq_zero fun result _ hevent =>
      hgood ((ShareFinal.goodWalk_iff prfSeed publicSeed table).mp hevent.1))) (by simp)

open BlindCharge in
set_option maxHeartbeats 4000000 in
/-- **The shared half's obligation at `127`, the signer's calls free.** -/
theorem hshared (q : Nat) (adversary : Adversary) (hbudget : TailBudget adversary q) :
    Pr[fun pair : SharedJoin.RecordedPair => Target.GoodWalk pair.1 ∧
        (RoutedSplit.InputBad (SharedJoin.recordedTraceOf pair) ∨ Target127.Late pair) |
      RandomiserRecord.recordedPairedRun adversary] ≤
      ((q - 2 ^ subtreeHeight + 259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  have hq := keygen_le_of_tail hbudget
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
            Pr[fun z => (ShareFinal.setupOf prfSeed publicSeed table).Good ∧ z.2.2 = true |
              ShareBound.flagRun adversary (ShareFinal.capLimit q)
                (ShareFinal.setupOf prfSeed publicSeed table)] :=
        ex_mono _ fun prfSeed => ex_mono _ fun publicSeed => ex_mono _ fun table =>
          walk_bound hbudget prfSeed publicSeed table
    _ = ex ($ᵗ Digest : ProbComp Digest) fun publicSeed => ex ($ᵗ Digest : ProbComp Digest)
          fun prfSeed => ex ($ᵗ (Cells × Padding) : ProbComp (Cells × Padding)) fun table =>
            Pr[fun z => (ShareFinal.setupOf prfSeed publicSeed table).Good ∧ z.2.2 = true |
              ShareBound.flagRun adversary (ShareFinal.capLimit q)
                (ShareFinal.setupOf prfSeed publicSeed table)] :=
        ShareFinal.ex_comm _ _ _
    _ = ex ($ᵗ Digest : ProbComp Digest) fun publicSeed =>
          Pr[fun w => w.1.Good ∧ w.2.2.2 = true |
            ShareBound.flagGame publicSeed adversary (ShareFinal.capLimit q)] := by
        refine ex_congr _ fun publicSeed => ?_
        rw [ShareBound.flagGame, probEvent_eq_ex_bind]
        refine ex_congr _ fun prfSeed => ?_
        rw [probEvent_eq_ex_bind]
        refine ex_congr _ fun table => ?_
        rw [bind_pure_comp, probEvent_map]
        rfl
    _ ≤ ex ($ᵗ Digest : ProbComp Digest) fun _ =>
          ((ShareFinal.capLimit q + 3929 + 259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) :=
        ex_mono _ fun publicSeed => ShareBound.blind_bound publicSeed adversary
          (ShareFinal.capLimit q)
    _ ≤ ((ShareFinal.capLimit q + 3929 + 259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) :=
        ShareBound.ex_const_le _ _
    _ ≤ ((q - 2 ^ subtreeHeight + 259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
        refine ENNReal.div_le_div_right (Nat.cast_le.mpr ?_) _
        unfold ShareFinal.capLimit
        have : (chains + 1) * 2 ^ subtreeHeight = 18432 := by decide
        have h2 : 2 ^ subtreeHeight = 512 := by decide
        rw [this] at hq ⊢
        rw [h2]
        omega

end SlhDsaSecurity.BySourceShared
