import XmssSecurity.Proof.TargetSum.Direct.CountedSourceTrace
import XmssSecurity.Proof.TargetSum.Direct.Prune

/-! The source budget is inherited by every supported continuation. In particular, a
signing call may spend a random number of hashes without requiring a fixed per-call cost. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.CappedChain

open Seeded

def CountedSourceState.charge (state : CountedSourceState) : Nat :=
  state.counts.direct + 2 * state.counts.signing

theorem phaseCountsImpl_counts_mono
    (signing : SignRequest → OracleComp OracleWorld (Option Signature))
    (input : (OracleWorld + SigningSpec).Domain) (state : PhaseCounts)
    (result : (OracleWorld + SigningSpec).Range input × PhaseCounts)
    (hresult : result ∈ support ((phaseCountsImpl signing input).run state)) :
    state.direct ≤ result.2.direct ∧ state.signing ≤ result.2.signing := by
  cases input with
  | inl input =>
      simp only [phaseCountsImpl, StateT.run, support_map] at hresult
      obtain ⟨sample, _, rfl⟩ := hresult
      exact ⟨Nat.le_add_right _ _, le_rfl⟩
  | inr request =>
      simp only [phaseCountsImpl, StateT.run, support_map] at hresult
      obtain ⟨sample, _, rfl⟩ := hresult
      exact ⟨le_rfl, Nat.le_add_right _ _⟩

theorem countedSourceImpl_counts_mono (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (state : CountedSourceState)
    (result : (OracleWorld + SigningSpec).Range input × CountedSourceState)
    (hresult : result ∈ support ((countedSourceImpl secretKey input).run state)) :
    state.counts.direct ≤ result.2.counts.direct ∧
      state.counts.signing ≤ result.2.counts.signing := by
  apply phaseCountsImpl_counts_mono _ input state.counts (result.1, result.2.counts)
  change (result.1, result.2.counts) ∈ support
    ((referencePhaseCountsImpl secretKey input).run state.counts)
  rw [← countedSourceImpl_counts_projection secretKey input state, support_map]
  exact ⟨result, hresult, rfl⟩

theorem countedSource_counts_mono {α : Type} (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CountedSourceState)
    (result : α × CountedSourceState)
    (hresult : result ∈ support ((simulateQ (countedSourceImpl secretKey) computation).run state)) :
    state.counts.direct ≤ result.2.counts.direct ∧
      state.counts.signing ≤ result.2.counts.signing := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨le_rfl, le_rfl⟩
  | query_bind input next ih =>
      rw [Direct.run_simulateQ_query_bind, mem_support_bind_iff] at hresult
      obtain ⟨head, hhead, htail⟩ := hresult
      have hstep := countedSourceImpl_counts_mono secretKey input state head hhead
      have hrest := ih head.1 head.2 result htail
      exact ⟨hstep.1.trans hrest.1, hstep.2.trans hrest.2⟩

theorem countedSource_charge_mono {α : Type} (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CountedSourceState)
    (result : α × CountedSourceState)
    (hresult : result ∈ support ((simulateQ (countedSourceImpl secretKey) computation).run state)) :
    state.charge ≤ result.2.charge := by
  have h := countedSource_counts_mono secretKey computation state result hresult
  exact Nat.add_le_add h.1 (Nat.mul_le_mul_left 2 h.2)

def CountedSourceBudget {α : Type} (secretKey : SecretKey) (limit : Nat)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CountedSourceState) : Prop :=
  ∀ result ∈ support ((simulateQ (countedSourceImpl secretKey) computation).run state),
    result.2.charge ≤ limit

theorem CountedSourceBudget.initial_le {α : Type} {secretKey : SecretKey} {limit : Nat}
    {computation : OracleComp (OracleWorld + SigningSpec) α} {state : CountedSourceState}
    (hbudget : CountedSourceBudget secretKey limit computation state) : state.charge ≤ limit := by
  obtain ⟨result, hresult⟩ := probComp_support_nonempty
    ((simulateQ (countedSourceImpl secretKey) computation).run state)
  exact (countedSource_charge_mono secretKey computation state result hresult).trans
    (hbudget result hresult)

theorem countedSourceBudget_bind_iff {α β : Type} (secretKey : SecretKey) (limit : Nat)
    (head : OracleComp (OracleWorld + SigningSpec) α)
    (next : α → OracleComp (OracleWorld + SigningSpec) β) (state : CountedSourceState) :
    CountedSourceBudget secretKey limit (head >>= next) state ↔
      ∀ result ∈ support ((simulateQ (countedSourceImpl secretKey) head).run state),
        CountedSourceBudget secretKey limit (next result.1) result.2 := by
  simp only [CountedSourceBudget, simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
  constructor
  · intro h result hresult final hfinal
    exact h final ⟨result, hresult, hfinal⟩
  · intro h final hfinal
    obtain ⟨result, hresult, hfinal⟩ := hfinal
    exact h result hresult final hfinal

theorem CountedSourceBudget.prefix {α β : Type} {secretKey : SecretKey} {limit : Nat}
    {head : OracleComp (OracleWorld + SigningSpec) α}
    {next : α → OracleComp (OracleWorld + SigningSpec) β} {state : CountedSourceState}
    (hbudget : CountedSourceBudget secretKey limit (head >>= next) state)
    (result : α × CountedSourceState)
    (hresult : result ∈ support ((simulateQ (countedSourceImpl secretKey) head).run state)) :
    result.2.charge ≤ limit ∧ CountedSourceBudget secretKey limit (next result.1) result.2 := by
  have hnext := (countedSourceBudget_bind_iff secretKey limit head next state).1 hbudget
    result hresult
  exact ⟨hnext.initial_le, hnext⟩

theorem CountedSourceBudget.query_step {α : Type} {secretKey : SecretKey} {limit : Nat}
    {input : (OracleWorld + SigningSpec).Domain}
    {next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α}
    {state : CountedSourceState}
    (hbudget : CountedSourceBudget secretKey limit
      (liftM ((OracleWorld + SigningSpec).query input) >>= next) state)
    (result : (OracleWorld + SigningSpec).Range input × CountedSourceState)
    (hresult : result ∈ support ((countedSourceImpl secretKey input).run state)) :
    result.2.charge ≤ limit ∧ CountedSourceBudget secretKey limit (next result.1) result.2 := by
  apply hbudget.prefix result
  simpa only [simulateQ_spec_query] using hresult

/-- info: 'XmssSecurity.TargetSum.CappedChain.CountedSourceBudget.prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CountedSourceBudget.prefix

end XmssSecurity.TargetSum.CappedChain
