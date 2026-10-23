import SlhDsaSecurity.Proof.SharePresent
import SlhDsaSecurity.Proof.KeygenCost
import SlhDsaSecurity.Proof.WarmedCharges

/-!
# The cap changes nothing in the real game

The shared games run the adversary capped at `L = q - (chains + 1) · 2 ^ subtreeHeight` weighted
queries. That is a change to the computation, and it is paid for here, on the real side, where
the budget lives: the flattened real handler reports the cap's weight in its own state — the
adversary's work, plus one per served request — and on every path of the real game that weight
is at most `L` (`cost_le_of_budget`), because the whole game's hash calls are at most `q`, key
generation alone spends `(chains + 1) · 2 ^ subtreeHeight`, and each served request costs the
signer two uncharged calls. So `CapComp.evalDist_capComp` applies and the capped real game has
the law of the real game (`evalDist_realFlat_cap`).
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.ShareRealCap

open Security CanonicalGraph WarmedGame WalkTable TableTail RecordedQueries RecordedPhase
  SharePresent

attribute [local irreducible] WarmedGame.afterSeeds Scheme.verify Scheme.keygenInternal
  Security.countQueries

/-! ## The stripped signer answers exactly the framed requests -/

theorem answer_isSome (warm : QueryCache HashSpec) (sk : SecretKey) (request : Message)
    (cache : QueryCache HashSpec) (z : Option Bytes × QueryCache HashSpec)
    (hz : z ∈ support ((simulateQ KeygenUniform.rom
      (StrippedGame.strippedSign warm sk request)).run cache)) :
    z.1.isSome = request.frame.isSome := by
  unfold StrippedGame.strippedSign Scheme.sign at hz
  cases hframe : request.frame with
  | none =>
    simp only [hframe] at hz
    simp only [simulateQ_pure, OracleComp.liftComp_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    rw [hz]
  | some message =>
    simp only [hframe] at hz
    simp only [bind_pure_comp, simulateQ_map, OracleComp.liftComp_map, StateT.run_map,
      support_map, Set.mem_image] at hz
    obtain ⟨w, -, rfl⟩ := hz
    rfl

/-! ## The real handler reports the cap's weight -/

theorem exists_of_mem_support_map {α β : Type} (f : α → β) (mx : ProbComp α) (z : β)
    (hz : z ∈ support (f <$> mx)) : ∃ w ∈ support mx, f w = z := by
  rw [support_map] at hz
  exact hz

/-- The cap's weight, read off the flattened real state. -/
def realCost (state : RealState) : Nat :=
  (Multiplicative.toAdd state.1).1.work + AdversaryQueries.servedCount state.2.1

theorem reportsCost_real (warm : QueryCache HashSpec) (sk : SecretKey) :
    CapComp.ReportsCost (realImpl (StrippedGame.strippedSign warm sk)) ShareGame.weight
      realCost := by
  intro queried state z hz
  rcases queried with world | request
  · rw [realImpl_world_run] at hz
    obtain ⟨w, -, rfl⟩ := exists_of_mem_support_map _ _ _ hz
    rcases world with coin | input
    · simp [realCost, phaseCost, ShareGame.weight, AdversaryQueries.work_add,
        AdversaryQueries.work_single_hash, hashCost, XmssSecurity.RandomOracleModel.hashCost]
    · simp [realCost, phaseCost, ShareGame.weight, AdversaryQueries.work_add,
        AdversaryQueries.work_single_hash, hashCost, XmssSecurity.RandomOracleModel.hashCost]
      omega
  · rw [realImpl_request_run] at hz
    obtain ⟨w, hw, rfl⟩ := exists_of_mem_support_map _ _ _ hz
    have hsome := answer_isSome warm sk request state.2.2 w hw
    simp only [realCost, phaseCost, ShareGame.weight, toAdd_mul, toAdd_ofAdd, Prod.fst_add,
      AdversaryQueries.work_add, AdversaryQueries.work_single_signing,
      AdversaryQueries.servedCount_append, hsome]
    omega

/-! ## The capped adversary -/

/-- The adversary, capped at `limit` weighted queries. -/
noncomputable def capAdv (adversary : Adversary) (limit : Nat) : Adversary :=
  ⟨fun pk => CapComp.capComp ShareGame.weight ShareGame.fallbackForgery limit (adversary.main pk)⟩

/-- **Where the real phase never exceeds the limit, the capped real game is the real game.** -/
theorem evalDist_realFlat_cap (adversary : Adversary) (keys : SecretKey × PublicKey)
    (warm : QueryCache HashSpec) (limit : Nat)
    (hbound : ∀ z ∈ support ((simulateQ (realImpl (StrippedGame.strippedSign warm keys.1))
        (adversary.main keys.2)).run (1, [], warm)), realCost z.2 ≤ limit) :
    𝒟[realFlat (capAdv adversary limit) keys warm] = 𝒟[realFlat adversary keys warm] := by
  unfold realFlat
  rw [evalDist_bind, evalDist_bind]
  congr 1
  refine CapComp.evalDist_capComp (realImpl (StrippedGame.strippedSign warm keys.1))
    ShareGame.weight realCost (reportsCost_real warm keys.1) (fun _ _ => probFailure_eq_zero)
    ShareGame.fallbackForgery (adversary.main keys.2) limit (1, [], warm) fun z hz => ?_
  have h := hbound z hz
  simp only [realCost, toAdd_one, Prod.fst_zero, AdversaryQueries.servedCount] at h ⊢
  simp [Counts.work] at h ⊢
  omega

/-! ## The budget bounds the real phase's weight -/

/-- A point the linked run reaches is one the recorded tail reaches, with its count beside it. -/
theorem exists_recordedTail_of_linked (adversary : Adversary) (prfSeed publicSeed : Digest)
    (table : Cells × Padding)
    (r : ((((Forgery × Multiplicative Tally) × (Bool × Tally)) × SigningLog) ×
      QueryCache HashSpec))
    (hr : r ∈ support (linkedRun adversary prfSeed publicSeed table)) :
    ∃ result ∈ support (RecordedTail.recordedTail adversary (walkOfTable prfSeed publicSeed table)),
      result.1.1 = LinkedGame.outcomeOf r.1 ∧ result.2 = r.2 := by
  classical
  have hpos : Pr[fun result => (LinkedGame.outcomeOf result.1, result.2) =
      (LinkedGame.outcomeOf r.1, r.2) | linkedRun adversary prfSeed publicSeed table] ≠ 0 :=
    probEvent_ne_zero_iff.mpr ⟨r, hr, rfl⟩
  rw [← probEvent_recordedTail_linked adversary prfSeed publicSeed table
    (fun x => x = (LinkedGame.outcomeOf r.1, r.2))] at hpos
  obtain ⟨result, hresult, heq⟩ := probEvent_ne_zero_iff.mp hpos
  exact ⟨result, hresult, congrArg Prod.fst heq, congrArg Prod.snd heq⟩

set_option maxHeartbeats 2000000 in
/-- **On every path of the real phase, the cap's weight is within the budget left after key
generation.** -/
theorem cost_le_of_budget {adversary : Adversary} {q : Nat} (hbudget : HasTotalBudget adversary q)
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
  have htotal := WarmedCharges.count_le_of_budget_tail hbudget
    (mem_support_graphWalk_walkOfTable prfSeed publicSeed table) htail
  obtain ⟨keygenCount, keys, keyCache, hkeys, hsum⟩ :=
    AdversaryQueries.work_add_keygen_add_served_le_total adversary
      (walkOfTable prfSeed publicSeed table).1.1 (walkOfTable prfSeed publicSeed table).2 _ htail
  have hkeygen := KeygenCost.count_keygen_ge _ _ _ _ _ hkeys
  have hcounts : result.1.1.1.counts =
      (Multiplicative.toAdd z.2.1).1 + (Multiplicative.toAdd w.2.1).1 := by
    rw [houtcome]
    rfl
  have hsigned : result.1.1.1.signed = z.2.2.1 := by
    rw [houtcome]
    rfl
  simp only [hcounts, hsigned, AdversaryQueries.work_add] at hsum
  simp only at htotal hkeygen
  unfold realCost
  omega

end SlhDsaSecurity.ShareRealCap
