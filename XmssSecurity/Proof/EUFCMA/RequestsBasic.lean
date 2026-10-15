import XmssSecurity.Proof.Direct.Prune

/-! A shared syntactic budget for direct hash queries and signing requests.
Private sampling is free. Pruning this budget preserves any execution whose
semantic count stays within the limit. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.EUFCMA.Requests

def isCharged : (OracleWorld + SigningSpec).Domain → Bool
  | .inl (.inl _) => false
  | _ => true

def IsCharged (input : (OracleWorld + SigningSpec).Domain) : Prop := isCharged input = true

instance : DecidablePred IsCharged := fun input =>
  inferInstanceAs (Decidable (isCharged input = true))

@[simp] theorem charged_hash (input : HashInput) : IsCharged (.inl (.inr input)) := rfl
@[simp] theorem charged_sign (request : SignRequest) : IsCharged (.inr request) := rfl
@[simp] theorem not_charged_uniform (input : unifSpec.Domain) :
    ¬IsCharged (.inl (.inl input)) := by simp [IsCharged, isCharged]

def IsQueryBound (adversary : XmssSecurity.Adversary) (q : ℕ) : Prop :=
  ∀ publicKey, (adversary.main publicKey).IsQueryBoundP IsCharged q

theorem direct_bound_of_requests {α : Type}
    (computation : OracleComp (OracleWorld + SigningSpec) α) (q : ℕ)
    (h : computation.IsQueryBoundP IsCharged q) :
    computation.IsQueryBoundP Direct.IsDirectHashQuery q := by
  induction computation using OracleComp.inductionOn generalizing q with
  | pure value => simp
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at h ⊢
      rcases input with (sample | hashInput) | request
      · refine ⟨Or.inl (by simp), fun answer => ?_⟩
        simpa using ih answer q (by simpa using h.2 answer)
      · exact ⟨h.1, fun answer => ih answer _ (h.2 answer)⟩
      · refine ⟨Or.inl (by simp), fun answer => ?_⟩
        simpa using (ih answer (q - 1) (by simpa using h.2 answer)).mono (Nat.sub_le q 1)

theorem IsQueryBound.direct {adversary : XmssSecurity.Adversary} {q : ℕ}
    (h : IsQueryBound adversary q) : Direct.IsDirectQueryBound adversary q :=
  fun publicKey => direct_bound_of_requests _ q (h publicKey)

noncomputable def prune {α : Type} (budget : ℕ)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    OracleComp (OracleWorld + SigningSpec) α :=
  OracleComp.recOn computation (fun value _ => pure value)
    (fun input _ next budget => match input with
      | .inl (.inl sample) =>
          liftM ((OracleWorld + SigningSpec).query (.inl (.inl sample))) >>= fun answer =>
            next answer budget
      | .inl (.inr hashInput) =>
          if budget = 0 then next default 0
          else liftM ((OracleWorld + SigningSpec).query (.inl (.inr hashInput))) >>= fun answer =>
            next answer (budget - 1)
      | .inr request =>
          if budget = 0 then next none 0
          else liftM ((OracleWorld + SigningSpec).query (.inr request)) >>= fun answer =>
            next answer (budget - 1)) budget

@[simp] theorem prune_pure {α : Type} (budget : ℕ) (value : α) :
    prune budget (pure value : OracleComp (OracleWorld + SigningSpec) α) = pure value := rfl

theorem prune_uniform_bind {α : Type} (budget : ℕ) (sample : unifSpec.Domain)
    (next : unifSpec.Range sample → OracleComp (OracleWorld + SigningSpec) α) :
    prune budget (liftM ((OracleWorld + SigningSpec).query (.inl (.inl sample))) >>= next) =
      liftM ((OracleWorld + SigningSpec).query (.inl (.inl sample))) >>= fun answer =>
        prune budget (next answer) := rfl

theorem prune_hash_bind {α : Type} (budget : ℕ) (input : HashInput)
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) α) :
    prune budget (liftM ((OracleWorld + SigningSpec).query (.inl (.inr input))) >>= next) =
      if budget = 0 then prune 0 (next default)
      else liftM ((OracleWorld + SigningSpec).query (.inl (.inr input))) >>= fun answer =>
        prune (budget - 1) (next answer) := rfl

theorem prune_sign_bind {α : Type} (budget : ℕ) (request : SignRequest)
    (next : Option Signature → OracleComp (OracleWorld + SigningSpec) α) :
    prune budget (liftM ((OracleWorld + SigningSpec).query (.inr request)) >>= next) =
      if budget = 0 then prune 0 (next none)
      else liftM ((OracleWorld + SigningSpec).query (.inr request)) >>= fun answer =>
        prune (budget - 1) (next answer) := rfl

theorem prune_isQueryBound {α : Type} (budget : ℕ)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    (prune budget computation).IsQueryBoundP IsCharged budget := by
  induction computation using OracleComp.inductionOn generalizing budget with
  | pure value => simp
  | query_bind input next ih =>
      rcases input with (sample | hashInput) | request
      · rw [prune_uniform_bind, isQueryBoundP_query_bind_iff]
        exact ⟨Or.inl (by simp), fun answer => by simpa using ih answer budget⟩
      · rw [prune_hash_bind]
        split_ifs with hzero
        · subst hzero; exact ih default 0
        · rw [isQueryBoundP_query_bind_iff]
          exact ⟨Or.inr (Nat.pos_of_ne_zero hzero), fun answer => by simpa using ih answer (budget - 1)⟩
      · rw [prune_sign_bind]
        split_ifs with hzero
        · subst hzero; exact ih none 0
        · rw [isQueryBoundP_query_bind_iff]
          exact ⟨Or.inr (Nat.pos_of_ne_zero hzero), fun answer => by simpa using ih answer (budget - 1)⟩

noncomputable def pruneAdversary (budget : ℕ) (adversary : XmssSecurity.Adversary) : XmssSecurity.Adversary where
  main := fun publicKey => prune budget (adversary.main publicKey)

theorem pruneAdversary_isQueryBound (budget : ℕ) (adversary : XmssSecurity.Adversary) :
    IsQueryBound (pruneAdversary budget adversary) budget :=
  fun publicKey => prune_isQueryBound budget (adversary.main publicKey)

theorem run_logged_counted_query_bind {α : Type}
    (impl : QueryImpl (OracleWorld + SigningSpec)
      (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)))
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) :
    (simulateQ romImpl (simulateQ impl (QueryCounting.counted IsCharged
        (liftM ((OracleWorld + SigningSpec).query input) >>= next))).run).run cache =
      (simulateQ romImpl (impl input).run).run cache >>= fun head =>
        (fun tail => (((tail.1.1.1, (if IsCharged input then 1 else 0) + tail.1.1.2),
            head.1.2 ++ tail.1.2), tail.2)) <$>
          (simulateQ romImpl (simulateQ impl
            (QueryCounting.counted IsCharged (next head.1.1))).run).run head.2 := by
  rw [QueryCounting.counted_query_bind]
  simp [simulateQ_bind, StateT.run_bind]

theorem simulate_prune_eq_logged {α : Type}
    (impl : QueryImpl (OracleWorld + SigningSpec)
      (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)))
    (computation : OracleComp (OracleWorld + SigningSpec) α) (budget : ℕ)
    (cache : QueryCache HashSpec)
    (hbound : ∀ result ∈ support ((simulateQ romImpl (simulateQ impl
      (QueryCounting.counted IsCharged computation)).run).run cache), result.1.1.2 ≤ budget) :
    (simulateQ romImpl (simulateQ impl (prune budget computation)).run).run cache =
      (simulateQ romImpl (simulateQ impl computation).run).run cache := by
  induction computation using OracleComp.inductionOn generalizing budget cache with
  | pure value => rfl
  | query_bind input next ih =>
      have hcont (head) (hhead : head ∈ support ((simulateQ romImpl (impl input).run).run cache))
          (tail) (htail : tail ∈ support ((simulateQ romImpl (simulateQ impl
            (QueryCounting.counted IsCharged (next head.1.1))).run).run head.2)) :
          (if IsCharged input then 1 else 0) + tail.1.1.2 ≤ budget := by
        rw [run_logged_counted_query_bind] at hbound
        exact hbound _ ((mem_support_bind_iff _ _ _).mpr ⟨head, hhead, by
          rw [support_map]; exact ⟨tail, htail, rfl⟩⟩)
      have hpos (hcharged : IsCharged input) : budget ≠ 0 := by
        obtain ⟨head, hhead⟩ := probComp_support_nonempty ((simulateQ romImpl (impl input).run).run cache)
        obtain ⟨tail, htail⟩ := probComp_support_nonempty ((simulateQ romImpl (simulateQ impl
          (QueryCounting.counted IsCharged (next head.1.1))).run).run head.2)
        have h := hcont head hhead tail htail
        rw [if_pos hcharged] at h
        omega
      rcases input with (sample | hashInput) | request
      · rw [prune_uniform_bind, Direct.run_logged_query_bind, Direct.run_logged_query_bind]
        refine bind_congr_of_forall_mem_support _ fun head hhead => ?_
        rw [ih head.1.1 budget head.2 fun tail htail => by simpa using hcont head hhead tail htail]
      · rw [prune_hash_bind, if_neg (hpos (by simp)), Direct.run_logged_query_bind, Direct.run_logged_query_bind]
        refine bind_congr_of_forall_mem_support _ fun head hhead => ?_
        rw [ih head.1.1 (budget - 1) head.2 fun tail htail => by
          have h := hcont head hhead tail htail
          simp only [charged_hash, if_true] at h
          omega]
      · rw [prune_sign_bind, if_neg (hpos (by simp)), Direct.run_logged_query_bind, Direct.run_logged_query_bind]
        refine bind_congr_of_forall_mem_support _ fun head hhead => ?_
        rw [ih head.1.1 (budget - 1) head.2 fun tail htail => by
          have h := hcont head hhead tail htail
          simp only [charged_sign, if_true] at h
          omega]

/-- info: 'XmssSecurity.EUFCMA.Requests.simulate_prune_eq_logged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms simulate_prune_eq_logged

end XmssSecurity.EUFCMA.Requests
