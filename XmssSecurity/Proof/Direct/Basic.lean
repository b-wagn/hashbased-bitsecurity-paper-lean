import XmssSecurity.Proof.CappedChain.DirectQueryAccounting
import XmssSecurity.Proof.EncodingLemmas
import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Direct hash queries of the adversary

The 119-bit direct-count proof charges the adversary only for its own hash queries.
This file fixes the vocabulary shared by that proof:

* `IsDirectHashQuery`: the adversary's actions that are hash queries (`.inl (.inr _)`), as
  opposed to private sampling (`.inl (.inl _)`) and signing requests (`.inr _`);
* `IsDirectQueryBound adversary D`: a *syntactic* bound, `D` direct hash queries on every branch
  of the adversary's program whatever the oracle answers. It is independent of the game the
  adversary is run in, which is what lets it pass unchanged through the game hops of the proof;
* `pruneDirect n`: the program truncated after `n` direct hash queries (further hash queries are
  answered by `default` without a query), which turns the statement's semantic query bound into a
  syntactic one;
* `verifierQueryBound`: the hash calls of one verification, `1 + 99 + 1 + 32 = 133`.
-/

open OracleComp OracleSpec

namespace XmssSecurity.Direct

/-- The adversary's own hash queries, as a Boolean test on its actions. -/
def isDirectHashQuery : (OracleWorld + SigningSpec).Domain → Bool
  | .inl (.inr _) => true
  | _ => false

/-- The adversary's own hash queries. -/
def IsDirectHashQuery (input : (OracleWorld + SigningSpec).Domain) : Prop :=
  isDirectHashQuery input = true

instance : DecidablePred IsDirectHashQuery := fun input =>
  inferInstanceAs (Decidable (isDirectHashQuery input = true))

@[simp]
theorem isDirectHashQuery_hash (input : HashInput) :
    IsDirectHashQuery (.inl (.inr input)) := rfl

@[simp]
theorem not_isDirectHashQuery_uniform (input : unifSpec.Domain) :
    ¬IsDirectHashQuery (.inl (.inl input)) := by
  simp [IsDirectHashQuery, isDirectHashQuery]

@[simp]
theorem not_isDirectHashQuery_sign (request : SignRequest) :
    ¬IsDirectHashQuery (.inr request) := by
  simp [IsDirectHashQuery, isDirectHashQuery]

theorem directHashActionCost_eq_if (input : (OracleWorld + SigningSpec).Domain) :
    CappedChain.directHashActionCost input = if IsDirectHashQuery input then 1 else 0 := by
  rcases input with (uniformOrHash | request)
  · rcases uniformOrHash with n | hashInput <;> rfl
  · rfl

/-- `D` direct hash queries on every branch of the adversary's program, for every public key and
whatever the oracles answer. -/
def IsDirectQueryBound (adversary : Adversary) (D : ℕ) : Prop :=
  ∀ publicKey, (adversary.main publicKey).IsQueryBoundP IsDirectHashQuery D

theorem IsDirectQueryBound.mono {adversary : Adversary} {D D' : ℕ}
    (h : IsDirectQueryBound adversary D) (hle : D ≤ D') : IsDirectQueryBound adversary D' :=
  fun publicKey => (h publicKey).mono hle

/-- The hash calls of one verification whose encoding decodes: the encoding hash, the
`v·(2^w - 1) - T = 99` chain steps, the leaf hash, and the `h = 32` Merkle levels. -/
def verifierQueryBound : ℕ := 1 + verificationChainHashes + 1 + treeHeight

theorem verifierQueryBound_eq : verifierQueryBound = 133 := by decide

/-! ## Pruning -/

/-- The program truncated after `budget` direct hash queries: a hash query beyond the budget is
answered by `default` without querying. Private sampling and signing requests are unaffected. -/
noncomputable def pruneDirect {α : Type} (budget : ℕ)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    OracleComp (OracleWorld + SigningSpec) α :=
  OracleComp.recOn computation (fun value _ => pure value)
    (fun input _ ih budget => match input with
      | .inl (.inr hashInput) =>
          if budget = 0 then ih default 0
          else liftM ((OracleWorld + SigningSpec).query (.inl (.inr hashInput))) >>= fun answer =>
            ih answer (budget - 1)
      | .inl (.inl uniformInput) =>
          liftM ((OracleWorld + SigningSpec).query (.inl (.inl uniformInput))) >>= fun answer =>
            ih answer budget
      | .inr request =>
          liftM ((OracleWorld + SigningSpec).query (.inr request)) >>= fun answer =>
            ih answer budget) budget

theorem pruneDirect_pure {α : Type} (budget : ℕ) (value : α) :
    pruneDirect budget (pure value : OracleComp (OracleWorld + SigningSpec) α) = pure value := rfl

theorem pruneDirect_hash_bind {α : Type} (budget : ℕ) (hashInput : HashInput)
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) α) :
    pruneDirect budget (liftM ((OracleWorld + SigningSpec).query (.inl (.inr hashInput))) >>= next) =
      if budget = 0 then pruneDirect 0 (next default)
      else liftM ((OracleWorld + SigningSpec).query (.inl (.inr hashInput))) >>= fun answer =>
        pruneDirect (budget - 1) (next answer) := rfl

theorem pruneDirect_uniform_bind {α : Type} (budget : ℕ) (uniformInput : unifSpec.Domain)
    (next : unifSpec.Range uniformInput → OracleComp (OracleWorld + SigningSpec) α) :
    pruneDirect budget (liftM ((OracleWorld + SigningSpec).query (.inl (.inl uniformInput))) >>= next) =
      liftM ((OracleWorld + SigningSpec).query (.inl (.inl uniformInput))) >>= fun answer =>
        pruneDirect budget (next answer) := rfl

theorem pruneDirect_sign_bind {α : Type} (budget : ℕ) (request : SignRequest)
    (next : Option Signature → OracleComp (OracleWorld + SigningSpec) α) :
    pruneDirect budget (liftM ((OracleWorld + SigningSpec).query (.inr request)) >>= next) =
      liftM ((OracleWorld + SigningSpec).query (.inr request)) >>= fun answer =>
        pruneDirect budget (next answer) := rfl

/-- The pruned program is syntactically bounded. -/
theorem pruneDirect_isQueryBoundP {α : Type} (budget : ℕ)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    (pruneDirect budget computation).IsQueryBoundP IsDirectHashQuery budget := by
  induction computation using OracleComp.inductionOn generalizing budget with
  | pure value => simp [pruneDirect_pure]
  | query_bind input next ih =>
      rcases input with (uniformOrHash | request)
      · rcases uniformOrHash with uniformInput | hashInput
        · rw [pruneDirect_uniform_bind, isQueryBoundP_query_bind_iff]
          refine ⟨Or.inl (by simp), fun answer => ?_⟩
          simpa using ih answer budget
        · rw [pruneDirect_hash_bind]
          split_ifs with hzero
          · subst hzero
            exact ih default 0
          · rw [isQueryBoundP_query_bind_iff]
            refine ⟨Or.inr (Nat.pos_of_ne_zero hzero), fun answer => ?_⟩
            simpa using ih answer (budget - 1)
      · rw [pruneDirect_sign_bind, isQueryBoundP_query_bind_iff]
        refine ⟨Or.inl (by simp), fun answer => ?_⟩
        simpa using ih answer budget

/-- The adversary truncated after `budget` direct hash queries. -/
noncomputable def pruneAdversary (budget : ℕ) (adversary : Adversary) : Adversary where
  main := fun publicKey => pruneDirect budget (adversary.main publicKey)

theorem pruneAdversary_isDirectQueryBound (budget : ℕ) (adversary : Adversary) :
    IsDirectQueryBound (pruneAdversary budget adversary) budget :=
  fun publicKey => pruneDirect_isQueryBoundP budget (adversary.main publicKey)

end XmssSecurity.Direct
