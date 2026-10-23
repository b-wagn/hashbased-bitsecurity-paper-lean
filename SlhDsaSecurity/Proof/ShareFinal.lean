import SlhDsaSecurity.Proof.ShareEvent
import SlhDsaSecurity.Proof.AnswerFired
import SlhDsaSecurity.Proof.RecordedWalkTable

/-!
# The shared half at one setup

At one setup the chain is: the real game has the law of the capped real game (the cap never
fires, `ShareRealCap`); the capped real game is coupled with the lenient game so that the event
raises the lenient flag (`ShareWhole`, `ShareEvent`); the lenient flag has the law of the blind
flag (`ShareUntilBad`). `BySourceShared` averages this over `SK.prf`, the public seed and the
table, and charges the blind flag with `ShareBound.blind_bound`.
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
      Pr[fun z => z.2.2 = true | ShareBound.flagRun (shareComp adversary limit) setup] := by
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
      · simp only [SharePresent.realFlat, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at hreal
        obtain ⟨zs, -, w, hw, hrealEq⟩ := hreal
        exact flag_of_inputBad setup real zs.2 w (by rw [hrealEq]; exact hw)
          (by rw [hrealEq]) stateV hinv hflag hcache hlog hver hbad
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

/-! ## At one walk -/

/-- The cap the shared half runs the adversary at. -/
def capLimit (q : Nat) : Nat := q - (chains + 1) * 2 ^ subtreeHeight

/-- The setup a drawn walk is. -/
def setupOf (prfSeed publicSeed : Digest) (table : Cells × Padding) : Setup :=
  ⟨prfSeed, publicSeed, table⟩

theorem goodWalk_iff (prfSeed publicSeed : Digest) (table : Cells × Padding) :
    Target.GoodWalk (WalkTable.walkOfTable prfSeed publicSeed table) ↔
      (setupOf prfSeed publicSeed table).Good := Iff.rfl

/-! ## Averaged over the seeds and the table -/

open BlindCharge in
theorem ex_comm {α β : Type} (mx : ProbComp α) (my : ProbComp β) (f : α → β → ℝ≥0∞) :
    ex mx (fun a => ex my (f a)) = ex my (fun b => ex mx (fun a => f a b)) := by
  unfold ex
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun b => tsum_congr fun a => ?_
  ring

end SlhDsaSecurity.ShareFinal
