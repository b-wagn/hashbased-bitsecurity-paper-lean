import SlhDsaSecurity.Statement.SecurityNoVerify
import SlhDsaSecurity.Proof.ShareFinal
import SlhDsaSecurity.Proof.VerificationBudget

/-!
# Verification's calls are bounded, so leaving them uncharged costs a constant

The experiment charges the final verifier's calls to the `.verification` coordinate and
nothing else does: the adversary's phase charges `.hash` and `.signing` only
(`adversary_verification_eq_zero`). The verifier makes at most `3824` calls on every path
(`VerificationBudget.verification_count_bounds`). So the total count exceeds the count
outside verification by at most `3824`, and a `HasNoVerifyBudget` adversary at `q` is a
`HasTotalBudget` adversary at `q + 3824` (`hasTotalBudget_of_noVerify`).
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.NoVerifyBudget

open Security AdversaryQueries

/-! ## The adversary's phase charges nothing to verification -/

/-- An adversary hash call charges `.hash` only. -/
theorem adversaryImpl_charge (world : OracleWorld.Domain) (log : SigningLog)
    (cache : QueryCache HashSpec)
    (z : ((OracleWorld.Range world × Multiplicative Counts) × SigningLog) × QueryCache HashSpec)
    (hz : z ∈ support ((simulateQ KeygenUniform.rom
      ((WriterT.run (adversaryImpl world)).run log)).run cache)) :
    (Multiplicative.toAdd z.1.1.2) .verification = 0 := by
  rw [run_adversaryImpl, simulateQ_map, StateT.run_map, support_map] at hz
  obtain ⟨step, -, rfl⟩ := hz
  simp [Counts.single]

/-- A signing request charges `.signing` only. -/
theorem signingOracle_charge (sk : SecretKey) (request : Message) (log : SigningLog)
    (cache : QueryCache HashSpec)
    (z : ((Option Bytes × Multiplicative Counts) × SigningLog) × QueryCache HashSpec)
    (hz : z ∈ support ((simulateQ KeygenUniform.rom
      ((WriterT.run (Security.signingOracle sk request)).run log)).run cache)) :
    (Multiplicative.toAdd z.1.1.2) .verification = 0 := by
  rw [StrippedGame.signingOracle_eq, StrippedGame.run_signingOracleWith, simulateQ_bind,
    StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨step, -, hpure⟩ := hz
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hpure
  rw [hpure]
  simp [Counts.single]

set_option maxHeartbeats 1000000 in
/-- **The adversary's phase leaves the verification coordinate at zero.** -/
theorem adversary_verification_eq_zero (sk : SecretKey) {α : Type}
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (log : SigningLog) (cache : QueryCache HashSpec)
      (result : ((α × Multiplicative Counts) × SigningLog) × QueryCache HashSpec),
      result ∈ support ((simulateQ KeygenUniform.rom
        ((WriterT.run (simulateQ (adversaryImpl + Security.signingOracle sk)
          computation)).run log)).run cache) →
        (Multiplicative.toAdd result.1.1.2) .verification = 0 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro log cache result hmem
    rw [simulateQ_pure] at hmem
    rw [show ((WriterT.run (pure value : CountedRun α)).run log) =
        (pure ((value, (1 : Multiplicative Counts)), log) :
          OracleComp OracleWorld ((α × Multiplicative Counts) × SigningLog)) from rfl,
      simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [hmem]
    rfl
  | query_bind queried next ih =>
    intro log cache result hmem
    rw [simulateQ_bind, simulateQ_spec_query, run_counted_bind, simulateQ_bind, StateT.run_bind,
      mem_support_bind_iff] at hmem
    obtain ⟨outer, houter, hrest⟩ := hmem
    rw [simulateQ_map, StateT.run_map, support_map] at hrest
    obtain ⟨inner, hinner, rfl⟩ := hrest
    have htail := ih outer.1.1.1 outer.1.2 outer.2 inner hinner
    have hhead : (Multiplicative.toAdd outer.1.1.2) .verification = 0 := by
      rcases queried with world | request
      · rw [QueryImpl.add_apply_inl] at houter
        exact adversaryImpl_charge world log cache outer houter
      · rw [QueryImpl.add_apply_inr] at houter
        exact signingOracle_charge sk request log cache outer houter
    show (Multiplicative.toAdd (outer.1.1.2 * inner.1.1.2)) .verification = 0
    rw [toAdd_mul, Pi.add_apply, hhead, htail]

/-! ## The verifier's calls are bounded on every outcome -/

theorem verifier_count_le (pk : PublicKey) (request : Message) (wire : Bytes)
    (cache : QueryCache HashSpec) (result : Bool × Counts)
    (hresult : result ∈ support
      ((simulateQ (Xmss.RandomOracleModel.impl Bytes HashOutput)
        (countQueries VerificationBudget.verificationCost (Scheme.verify pk request wire))).run'
          cache)) :
    result.2 .verification ≤ 3824 := by
  cases hframe : request.frame with
  | none =>
    simp only [Scheme.verify, hframe, VerificationBudget.countQueries_pure, simulateQ_pure,
      StateT.run'_eq, StateT.run_pure, map_pure, support_pure, Set.mem_singleton_iff] at hresult
    subst result
    simp
  | some message =>
    cases hparse : Signature.fromBytes? wire with
    | none =>
      simp only [Scheme.verify, hframe, hparse, VerificationBudget.countQueries_pure,
        simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      simp
    | some signature =>
      exact (VerificationBudget.verification_count_bounds pk request wire message signature hframe
        hparse cache result hresult).2

set_option maxHeartbeats 1000000 in
/-- **No outcome charges more than `3824` to verification.** -/
theorem outcome_verification_le (adversary : Adversary) (outcome : Outcome)
    (houtcome : outcome ∈ support (Security.run adversary)) :
    outcome.counts .verification ≤ 3824 := by
  unfold Security.run Xmss.RandomOracleModel.run Security.experiment at houtcome
  rw [simulateQ_bind, StateT.run'_bind', mem_support_bind_iff] at houtcome
  obtain ⟨⟨⟨sk, pk⟩, keygenCache⟩, _hkeygen, hafterKeygen⟩ := houtcome
  dsimp only at hafterKeygen
  rw [simulateQ_bind, StateT.run'_bind', mem_support_bind_iff] at hafterKeygen
  obtain ⟨⟨⟨⟨forgery, adversaryCounts⟩, signed⟩, adversaryCache⟩, hadversary, hafterAdversary⟩ :=
    hafterKeygen
  dsimp only at hafterAdversary
  rw [simulateQ_bind, StateT.run'_bind', mem_support_bind_iff] at hafterAdversary
  obtain ⟨⟨⟨verified, verifierCounts⟩, verifierCache⟩, hverifier, hpure⟩ := hafterAdversary
  dsimp only at hpure
  simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure,
    support_pure, Set.mem_singleton_iff] at hpure
  subst outcome
  have hverifier' : (verified, verifierCounts) ∈ support
      ((simulateQ (Xmss.RandomOracleModel.impl Bytes HashOutput)
        (countQueries VerificationBudget.verificationCost
          (Scheme.verify pk forgery.message forgery.signature))).run' adversaryCache) := by
    rw [StateT.run'_eq, support_map, Set.mem_image]
    exact ⟨((verified, verifierCounts), verifierCache), hverifier, rfl⟩
  have hver := verifier_count_le pk forgery.message forgery.signature adversaryCache
    (verified, verifierCounts) hverifier'
  have hadv := adversary_verification_eq_zero sk (adversary.main pk) [] keygenCache
    (((forgery, adversaryCounts), signed), adversaryCache) hadversary
  show (Multiplicative.toAdd adversaryCounts + verifierCounts) .verification ≤ 3824
  rw [Pi.add_apply, hadv, Nat.zero_add]
  exact hver

/-- **A budget outside verification is a total budget, `3824` larger.** -/
theorem hasTotalBudget_of_noVerify {adversary : Adversary} {q : Nat}
    (hbudget : HasNoVerifyBudget adversary q) : HasTotalBudget adversary (q + 3824) := by
  refine le_antisymm probEvent_le_one ?_
  rw [← hbudget]
  refine probEvent_mono fun result hresult hevent => ⟨hevent.1, ?_⟩
  have houtcome : result.1 ∈ support (Security.run adversary) := by
    rw [← Security.fst_map_runAll adversary, support_map]
    exact ⟨result, hresult, rfl⟩
  have := outcome_verification_le adversary result.1 houtcome
  have := hevent.2
  omega

end SlhDsaSecurity.NoVerifyBudget
