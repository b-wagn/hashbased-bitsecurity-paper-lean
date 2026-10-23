import Xmss.Proof.Generic.IdealStatement

open OracleComp OracleSpec
open scoped BigOperators

namespace Xmss.Generic

variable [Code]

inductive ExactQueryCount {index : Type} {spec : OracleSpec index} :
    OracleComp spec α → Nat → Prop where
  | pure (value : α) : ExactQueryCount (pure value) 0
  | query (input : spec.Domain) (next : spec.Range input → OracleComp spec α)
      (count : Nat) (hnext : ∀ output, ExactQueryCount (next output) count) :
      ExactQueryCount (liftM (spec.query input) >>= next) (count + 1)

inductive ExactPredicateQueryCount {index : Type} {spec : OracleSpec index}
    (predicate : spec.Domain → Prop) [DecidablePred predicate] :
    OracleComp spec α → Nat → Prop where
  | pure (value : α) : ExactPredicateQueryCount predicate (pure value) 0
  | query (input : spec.Domain) (next : spec.Range input → OracleComp spec α)
      (count : Nat)
      (hnext : ∀ output, ExactPredicateQueryCount predicate (next output) count) :
      ExactPredicateQueryCount predicate
        (liftM (spec.query input) >>= next)
        (count + if predicate input then 1 else 0)

namespace ExactQueryCount

omit [Code] in
theorem bind {computation : OracleComp spec α} {count : Nat}
    (hcomputation : ExactQueryCount computation count)
    (next : α → OracleComp spec β) (nextCount : Nat)
    (hnext : ∀ value, ExactQueryCount (next value) nextCount) :
    ExactQueryCount (computation >>= next) (count + nextCount) := by
  induction hcomputation with
  | pure value => simpa using hnext value
  | query input rest restCount hrest ih =>
      rw [bind_assoc]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ExactQueryCount.query input (fun output => rest output >>= next)
          (restCount + nextCount) ih

omit [Code] in
theorem map {computation : OracleComp spec α} {count : Nat}
    (hcomputation : ExactQueryCount computation count) (f : α → β) :
    ExactQueryCount (f <$> computation) count := by
  convert hcomputation.bind
    (fun value => (Pure.pure (f value) : OracleComp spec β)) 0
    (fun value => ExactQueryCount.pure (f value)) using 1 <;>
    simp [map_eq_bind_pure_comp]

omit [Code] in
theorem withQueryLog {computation : OracleComp spec α} {count : Nat}
    (hcomputation : ExactQueryCount computation count) :
    ExactQueryCount computation.withQueryLog count := by
  induction hcomputation with
  | pure value => simpa using ExactQueryCount.pure (value, [])
  | query input next count hnext ih =>
      rw [OracleComp.withQueryLog_bind, OracleComp.withQueryLog_query, bind_assoc]
      exact .query input (fun output =>
        Prod.map id ([⟨input, output⟩] ++ ·) <$> (next output).withQueryLog)
        count (fun output => by
          exact (ih output).map (Prod.map id ([⟨input, output⟩] ++ ·)))

omit [Code] in
theorem liftComp_predicate
    {superIndex : Type} {superSpec : OracleSpec superIndex}
    [inclusion : spec ⊂ₒ superSpec]
    {computation : OracleComp spec α} {count : Nat}
    (hexact : ExactQueryCount computation count)
    (predicate : superSpec.Domain → Prop) [DecidablePred predicate]
    (hpredicate : ∀ input, predicate (inclusion.onQuery input)) :
    ExactPredicateQueryCount predicate
      (OracleComp.liftComp computation superSpec) count := by
  induction hexact with
  | pure value => exact .pure value
  | query input next count hnext ih =>
      rw [OracleComp.liftComp_bind, OracleComp.liftComp_query]
      change ExactPredicateQueryCount predicate
        (((liftM (spec.query input) : OracleComp superSpec (spec.Range input)) >>=
          fun output => OracleComp.liftComp (next output) superSpec)) (count + 1)
      rw [show
          (liftM (spec.query input) : OracleComp superSpec (spec.Range input)) =
            liftM (superSpec.query (inclusion.onQuery input)) >>= fun output =>
              Pure.pure (inclusion.onResponse input output) by
        change ((liftM (spec.query input) :
          OracleQuery superSpec (spec.Range input)) :
            OracleComp superSpec (spec.Range input)) = _
        rw [show
            (liftM (spec.query input) : OracleQuery superSpec (spec.Range input)) =
              ⟨inclusion.onQuery input, inclusion.onResponse input⟩ from
          inclusion.liftM_eq_lift _]
        rfl, bind_assoc]
      have hp : predicate (inclusion.onQuery input) := hpredicate input
      convert ExactPredicateQueryCount.query (inclusion.onQuery input)
        (fun output => OracleComp.liftComp
          (next (inclusion.onResponse input output)) superSpec)
        count (fun output => by
          simpa only [pure_bind] using ih (inclusion.onResponse input output)) using 1
      · simp
      · rw [if_pos hp]

namespace ExactPredicateQueryCount

variable {index : Type} {spec : OracleSpec index}
variable {predicate : spec.Domain → Prop} [DecidablePred predicate]

omit [Code] in
theorem bind {computation : OracleComp spec α} {count : Nat}
    (hcomputation : ExactPredicateQueryCount predicate computation count)
    (next : α → OracleComp spec β) (nextCount : Nat)
    (hnext : ∀ value, ExactPredicateQueryCount predicate (next value) nextCount) :
    ExactPredicateQueryCount predicate (computation >>= next) (count + nextCount) := by
  induction hcomputation with
  | pure value => simpa using hnext value
  | query input rest restCount hrest ih =>
      rw [bind_assoc]
      convert ExactPredicateQueryCount.query input
        (fun output => rest output >>= next) (restCount + nextCount) ih using 1
      by_cases hinput : predicate input
      · simp [hinput]
        omega
      · simp [hinput]

omit [Code] in
theorem of_isQueryBoundP_zero
    {computation : OracleComp spec α}
    (hbound : computation.IsQueryBoundP predicate 0) :
    ExactPredicateQueryCount predicate computation 0 := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact .pure value
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      have hinput : ¬predicate input := hbound.1.resolve_right (by omega)
      simpa [hinput] using ExactPredicateQueryCount.query input next 0
        (fun output => ih output (by simpa [hinput] using hbound.2 output))

end ExactPredicateQueryCount

omit [Code] in
theorem oracleHash (input : HashInput) :
    ExactQueryCount (Hashing.oracleHash input : OracleComp HashSpec Digest) 1 := by
  exact .query input (fun output => (Pure.pure output : OracleComp HashSpec Digest)) 0
    (fun output => ExactQueryCount.pure output)

theorem tweakableHash (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) :
    ExactQueryCount
      (Hashing.tweakableHash parameter domain payload : OracleComp HashSpec Digest) 1 := by
  exact oracleHash _

theorem chainWalk (parameter : PublicParameter) (leafIndex : LeafIndex)
    (chain : ChainIndex) (position steps : Nat) (value : Digest)
    (hposition : position + steps ≤ chainLength - 1) :
    ExactQueryCount
      (Wots.chainWalk (m := OracleComp HashSpec) parameter leafIndex chain
        position steps value) steps := by
  induction steps generalizing value with
  | zero => exact .pure value
  | succ steps ih =>
      rw [Wots.chainWalk]
      have hstep : position + steps < chainLength - 1 := by omega
      simp only [hstep, ↓reduceDIte]
      exact (ih value (by omega)).bind
        (fun previous => Hashing.chainHash parameter leafIndex chain
          ⟨position + steps, hstep⟩ previous) 1
        (fun previous => tweakableHash parameter (.chain leafIndex chain
          ⟨position + steps, hstep⟩) (Hashing.digestBytes previous))

omit [Code] in
theorem sequenceFin {n : Nat} (computation : Fin n → OracleComp spec α)
    (count : Fin n → Nat)
    (hcomputation : ∀ index, ExactQueryCount (computation index) (count index)) :
    ExactQueryCount (Generic.sequenceFin computation)
      (∑ index, count index) := by
  induction n with
  | zero => exact .pure Fin.elim0
  | succ n ih =>
      rw [Generic.sequenceFin, Fin.sum_univ_succ]
      exact (hcomputation 0).bind
        (fun head => do
          let tail ← Generic.sequenceFin fun index : Fin n => computation index.succ
          Pure.pure (show Fin (n + 1) → α from Fin.cases head tail))
        (∑ index : Fin n, count index.succ)
        (fun head => (ih (fun index => computation index.succ)
          (fun index => count index.succ) (fun index => hcomputation index.succ)).bind
            (fun tail => Pure.pure
              (show Fin (n + 1) → α from Fin.cases head tail)) 0
            (fun tail => ExactQueryCount.pure
              (show Fin (n + 1) → α from Fin.cases head tail)))

end ExactQueryCount
end Xmss.Generic
