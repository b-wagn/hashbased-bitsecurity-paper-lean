import XmssSecurity.Proof.Direct.DecidingPrefix
import XmssSecurity.Proof.Direct.DecidingFirstLaneCoupling

/-!
# Selecting the deciding probe in the public oracle world

The selector reveals a chain coordinate only when it is at or above the signed digit. Thus a
selected coordinate below the signed digit is still hidden. These reveals cost no hazards;
the selector's single final probe costs one.
-/

open OracleComp OracleSpec

namespace XmssSecurity.Deciding

open FirstLaneOracleSimulation

def ProbeEligible (signed : Option Encoding) (forged : Encoding) (chain : ChainIndex) : Prop :=
  ∃ encoding, signed = some encoding ∧ encoding chain ≤ forged chain

open Classical in
noncomputable def publicDecidingSearch (leaf : LeafIndex) (signed : Option Encoding)
    (forged : Encoding) (values : ChainIndex → Digest) :
    List ChainIndex → OracleComp (World CappedChain.GlobalChainValueIndex) (Option ChainIndex)
  | [] => pure none
  | chain :: rest =>
      if ProbeEligible signed forged chain then do
        let value ← revealQuery (chain, leaf, forged chain)
        if values chain = value then publicDecidingSearch leaf signed forged values rest
        else pure (some chain)
      else pure (some chain)

open Classical in
noncomputable def decidingSearchResult (table : CappedChain.GlobalChainValueIndex → Digest)
    (leaf : LeafIndex) (signed : Option Encoding) (forged : Encoding)
    (values : ChainIndex → Digest) :
    List ChainIndex → Option ChainIndex × ActionTrace CappedChain.GlobalChainValueIndex
  | [] => (none, [])
  | chain :: rest =>
      if ProbeEligible signed forged chain then
        let action := ObservedAction.chain (.reveal (chain, leaf, forged chain)
          (table (chain, leaf, forged chain)))
        if values chain = table (chain, leaf, forged chain) then
          let result := decidingSearchResult table leaf signed forged values rest
          (result.1, action :: result.2)
        else (some chain, [action])
      else (some chain, [])

theorem eager_reveal (table : CappedChain.GlobalChainValueIndex → Digest)
    (index : CappedChain.GlobalChainValueIndex) :
    (simulateQ (eagerTraceImpl table) (revealQuery index)).run =
      pure (table index, [ObservedAction.chain (.reveal index (table index))]) := by
  simp [revealQuery, eagerTraceImpl, eagerImpl, traceFragment,
    QueryImpl.withTraceAppend_apply]

theorem publicDecidingSearch_eager (table : CappedChain.GlobalChainValueIndex → Digest)
    (leaf : LeafIndex) (signed : Option Encoding) (forged : Encoding)
    (values : ChainIndex → Digest) (chains : List ChainIndex) :
    (simulateQ (eagerTraceImpl table)
      (publicDecidingSearch leaf signed forged values chains)).run =
      pure (decidingSearchResult table leaf signed forged values chains) := by
  classical
  induction chains with
  | nil => simp [publicDecidingSearch, decidingSearchResult]
  | cons chain rest ih =>
      by_cases heligible : ProbeEligible signed forged chain
      · simp only [publicDecidingSearch, decidingSearchResult, if_pos heligible]
        simp only [simulateQ_bind, WriterT.run_bind', eager_reveal, pure_bind]
        by_cases hvalue : values chain = table (chain, leaf, forged chain)
        · simp [hvalue, ih, Prod.map]
        · simp [hvalue, Prod.map]
      · simp [publicDecidingSearch, decidingSearchResult, heligible]

open Classical in
theorem decidingSearchResult_chain (table : CappedChain.GlobalChainValueIndex → Digest)
    (leaf : LeafIndex) (signed : Option Encoding) (forged : Encoding)
    (values : ChainIndex → Digest) (chains : List ChainIndex) :
    (decidingSearchResult table leaf signed forged values chains).1 =
      chains.find? (fun chain => decide (¬(ProbeEligible signed forged chain ∧
        values chain = table (chain, leaf, forged chain)))) := by
  classical
  induction chains with
  | nil => rfl
  | cons chain rest ih =>
      by_cases heligible : ProbeEligible signed forged chain
      · by_cases hvalue : values chain = table (chain, leaf, forged chain)
        · simp [decidingSearchResult, heligible, hvalue, ih]
        · simp [decidingSearchResult, heligible, hvalue]
      · simp [decidingSearchResult, heligible]

theorem decidingSearchResult_hazardCount (table : CappedChain.GlobalChainValueIndex → Digest)
    (leaf : LeafIndex) (signed : Option Encoding) (forged : Encoding)
    (values : ChainIndex → Digest) (chains : List ChainIndex) :
    hazardCount (decidingSearchResult table leaf signed forged values chains).2 = 0 := by
  classical
  induction chains with
  | nil => rfl
  | cons chain rest ih =>
      by_cases heligible : ProbeEligible signed forged chain
      · by_cases hvalue : values chain = table (chain, leaf, forged chain)
        · simpa [decidingSearchResult, heligible, hvalue, hazardCount] using ih
        · simp [decidingSearchResult, heligible, hvalue, hazardCount]
      · simp [decidingSearchResult, heligible, hazardCount]

theorem decidingSearchResult_reveals_eligible
    (table : CappedChain.GlobalChainValueIndex → Digest)
    (leaf : LeafIndex) (signed : Option Encoding) (forged : Encoding)
    (values : ChainIndex → Digest) (chains : List ChainIndex)
    (action : ObservedAction CappedChain.GlobalChainValueIndex)
    (hmem : action ∈ (decidingSearchResult table leaf signed forged values chains).2) :
    ∃ chain, ProbeEligible signed forged chain ∧
      action = .chain (.reveal (chain, leaf, forged chain) (table (chain, leaf, forged chain))) := by
  classical
  induction chains with
  | nil => simp [decidingSearchResult] at hmem
  | cons chain rest ih =>
      by_cases heligible : ProbeEligible signed forged chain
      · by_cases hvalue : values chain = table (chain, leaf, forged chain)
        · simp only [decidingSearchResult, if_pos heligible, if_pos hvalue, List.mem_cons] at hmem
          rcases hmem with hhead | htail
          · exact ⟨chain, heligible, hhead⟩
          · exact ih htail
        · simp only [decidingSearchResult, if_pos heligible, if_neg hvalue,
            List.mem_singleton] at hmem
          exact ⟨chain, heligible, hmem⟩
      · simp [decidingSearchResult, heligible] at hmem

theorem decidingSearchResult_no_hidden_reveal
    (table : CappedChain.GlobalChainValueIndex → Digest)
    (leaf : LeafIndex) (signed : Option Encoding) (forged : Encoding)
    (values : ChainIndex → Digest) (chains : List ChainIndex) (chain : ChainIndex)
    (hhidden : ¬ ProbeEligible signed forged chain) (value : Digest) :
    ObservedAction.chain (.reveal (chain, leaf, forged chain) value) ∉
      (decidingSearchResult table leaf signed forged values chains).2 := by
  intro hmem
  obtain ⟨other, heligible, heq⟩ :=
    decidingSearchResult_reveals_eligible table leaf signed forged values chains _ hmem
  cases heq
  exact hhidden heligible

theorem decidingSearchResult_eq_decidingChain
    (table : CappedChain.GlobalChainValueIndex → Digest)
    (cache : QueryCache HashSpec) (secretKey : SecretKey) (log : QueryLog SigningSpec)
    (forgery : Forgery) (forged : Encoding)
    (htable : ∀ chain, honestChainValue cache secretKey forgery.epoch chain (forged chain) =
      table (chain, forgery.epoch, forged chain)) :
    (decidingSearchResult table forgery.epoch
      (signedEncoding cache secretKey.parameter log forgery.epoch) forged
      forgery.signature.chainValue (List.finRange numChains)).1.getD ⟨0, by simp [numChains]⟩ =
      decidingChain cache secretKey log forgery forged := by
  classical
  rw [decidingSearchResult_chain]
  unfold decidingChain decidingChain?
  congr 2
  funext chain
  congr 1
  unfold ChainTrivial ProbeEligible
  rw [htable]
  aesop

noncomputable def publicDecidingProbe (leaf : LeafIndex) (signed : Option Encoding)
    (forged : Encoding) (values : ChainIndex → Digest) :
    OracleComp (World CappedChain.GlobalChainValueIndex) ChainIndex := do
  let chosen ← publicDecidingSearch leaf signed forged values (List.finRange numChains)
  let chain := chosen.getD ⟨0, by simp [numChains]⟩
  probeQuery (chain, leaf, forged chain) (values chain)
  pure chain

noncomputable def decidingProbeResult (table : CappedChain.GlobalChainValueIndex → Digest)
    (leaf : LeafIndex) (signed : Option Encoding) (forged : Encoding)
    (values : ChainIndex → Digest) : ChainIndex × ActionTrace CappedChain.GlobalChainValueIndex :=
  let search := decidingSearchResult table leaf signed forged values (List.finRange numChains)
  let chain := search.1.getD ⟨0, by simp [numChains]⟩
  (chain, search.2 ++ [.chain (.probe (chain, leaf, forged chain) (values chain))])

theorem publicDecidingProbe_eager (table : CappedChain.GlobalChainValueIndex → Digest)
    (leaf : LeafIndex) (signed : Option Encoding) (forged : Encoding)
    (values : ChainIndex → Digest) :
    (simulateQ (eagerTraceImpl table) (publicDecidingProbe leaf signed forged values)).run =
      pure (decidingProbeResult table leaf signed forged values) := by
  unfold publicDecidingProbe decidingProbeResult
  simp only [simulateQ_bind, WriterT.run_bind', publicDecidingSearch_eager, pure_bind]
  simp [probeQuery, eagerTraceImpl, eagerImpl, traceFragment,
    QueryImpl.withTraceAppend_apply, Prod.map]

theorem decidingProbeResult_hazardCount (table : CappedChain.GlobalChainValueIndex → Digest)
    (leaf : LeafIndex) (signed : Option Encoding) (forged : Encoding)
    (values : ChainIndex → Digest) :
    hazardCount (decidingProbeResult table leaf signed forged values).2 = 1 := by
  simp [decidingProbeResult, hazardCount_append, decidingSearchResult_hazardCount, hazardCount]

theorem chainAction_mem_iff (trace : ActionTrace CappedChain.GlobalChainValueIndex)
    (action : RevealProbeOracleSimulation.ObservedAction CappedChain.GlobalChainValueIndex) :
    action ∈ trace.chainActions ↔ ObservedAction.chain action ∈ trace := by
  induction trace with
  | nil => simp [ActionTrace.chainActions]
  | cons head tail ih =>
      cases head <;> simp_all [ActionTrace.chainActions]

theorem decidingProbeResult_hidden_hit (table : CappedChain.GlobalChainValueIndex → Digest)
    (leaf : LeafIndex) (signed : Option Encoding) (forged : Encoding)
    (values : ChainIndex → Digest) (history : ActionTrace CappedChain.GlobalChainValueIndex)
    (hhidden : ¬ ProbeEligible signed forged
      (decidingProbeResult table leaf signed forged values).1)
    (hvalue : table ((decidingProbeResult table leaf signed forged values).1, leaf,
      forged (decidingProbeResult table leaf signed forged values).1) =
        values (decidingProbeResult table leaf signed forged values).1)
    (hnoreveal : ∀ value, ObservedAction.chain (.reveal
      ((decidingProbeResult table leaf signed forged values).1, leaf,
        forged (decidingProbeResult table leaf signed forged values).1) value) ∉ history) :
    CombinedHit table (history ++ (decidingProbeResult table leaf signed forged values).2) := by
  apply Or.inr
  refine CappedChain.globalRunObserved_eq_true_of_probe_mem_of_no_reveal table
    AdaptiveRevealMonitor.State.empty _ _ _ (by rfl) ?_ hvalue ?_
  · rw [chainAction_mem_iff]
    apply List.mem_append_right
    change _ ∈ (decidingSearchResult table leaf signed forged values
      (List.finRange numChains)).2 ++ [_]
    exact List.mem_append_right _ (by simp [decidingProbeResult])
  · intro value hmem
    rw [chainAction_mem_iff, List.mem_append] at hmem
    rcases hmem with hpast | hselector
    · exact hnoreveal value hpast
    · change _ ∈ (decidingSearchResult table leaf signed forged values
        (List.finRange numChains)).2 ++ [_] at hselector
      rw [List.mem_append] at hselector
      rcases hselector with hsearch | hprobe
      · exact decidingSearchResult_no_hidden_reveal table leaf signed forged values
          (List.finRange numChains) _ hhidden value hsearch
      · simp at hprobe

end XmssSecurity.Deciding
