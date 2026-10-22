import SlhDsaSecurity.Proof.DigestTape

/-!
# Two recordings at once, and the invariant that keeps them independent

The coverage charge needs its disclosing digests to occupy a fixed *index block* of the tape
and its targets to occupy the rest, because the leave-one-out resampling needs the disclosure
set to be a function of the index rather than of the run. A single recording cannot supply
that: the two kinds of query interleave, so their positions are run-dependent. Two recordings
can, each padded to its own length and laid end to end.

What has to be true of the pair is the lazy-sampling invariant, and it has to be true of the
pair *jointly*: two words fixed in advance are the beginnings of the two recordings with
probability at most `|HashOutput| ^ -(n₁ + n₂)`. That cannot be assembled from the one-list
invariant. Knowing each word separately bounds its own recording leaves the joint event bounded
only by a union over the ways the two could interleave, and that union costs a binomial factor
which swallows the whole bound. So the induction is done once, with both targets carried: each
fresh recorded answer advances exactly one of them, and the letter it has to match costs its
own factor of `|HashOutput| ^ -1`.

The recorder is the one from `DigestTape` with its state doubled, and with the decision to
record taken on the input *and the cache in force*. That generality is free here — the decision
is made before the answer is drawn, so it is a function of the past, which is all the induction
uses — and it is what lets "the signer randomised this input" be the left-hand test, since that
is a question about the cache rather than about bytes.

Nothing here depends on what the two tests are. They are made exclusive by priority rather than
assumed disjoint, so that one fresh answer never advances both recordings at once, which is
what the counting needs.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.SplitPrefix

open DigestTape

/-- The cache together with the two recordings so far. -/
abbrev SplitState := QueryCache HashSpec × Record × Record

open scoped Classical in
/-- What the two recordings become when a query is answered: the left one takes the entry if
the query is fresh and passes the left test, otherwise the right one takes it if it passes the
right test, otherwise neither. The tests are tried in order, so a single answer is recorded
once. -/
noncomputable def appended (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (input : Bytes) (state : SplitState) (answer : HashOutput) : Record × Record :=
  if state.1 input = none ∧ leftKeep input state.1 then
    (state.2.1 ++ [(input, answer)], state.2.2)
  else if state.1 input = none ∧ rightKeep input state.1 then
    (state.2.1, state.2.2 ++ [(input, answer)])
  else state.2

theorem left_prefix_appended (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (input : Bytes) (state : SplitState) (answer : HashOutput) :
    state.2.1 <+: (appended leftKeep rightKeep input state answer).1 := by
  classical
  rw [appended]
  split
  · exact List.prefix_append _ _
  · split
    · exact List.prefix_rfl
    · exact List.prefix_rfl

theorem right_prefix_appended (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (input : Bytes) (state : SplitState) (answer : HashOutput) :
    state.2.2 <+: (appended leftKeep rightKeep input state answer).2 := by
  classical
  rw [appended]
  split
  · exact List.prefix_rfl
  · split
    · exact List.prefix_append _ _
    · exact List.prefix_rfl

open scoped Classical in
/-- The shared random oracle, keeping two recordings. -/
noncomputable def recorder (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop) :
    QueryImpl OracleWorld (StateT SplitState ProbComp) :=
  fun queried state =>
    match queried with
    | Sum.inl coin => do
        let value ← ($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _)
        pure (value, state)
    | Sum.inr input => do
        let step ← (randomOracle input).run state.1
        pure (step.1, (step.2, appended leftKeep rightKeep input state step.1))

open scoped Classical in
theorem recorder_run_inl (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (coin : unifSpec.Domain) (state : SplitState) :
    ((recorder leftKeep rightKeep) (Sum.inl coin)).run state =
      ($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _) >>= fun value =>
        (pure (value, state) : ProbComp _) := rfl

open scoped Classical in
theorem recorder_run_inr (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (input : Bytes) (state : SplitState) :
    ((recorder leftKeep rightKeep) (Sum.inr input)).run state =
      (((randomOracle input).run state.1 >>= fun step =>
        pure (step.1, (step.2, appended leftKeep rightKeep input state step.1))) :
          ProbComp (OracleWorld.Range (Sum.inr input) × SplitState)) := rfl

/-- The instrumented run from a given state, with an independent padding block for each
recording. -/
noncomputable def paddedFrom {α : Type} (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (computation : OracleComp OracleWorld α) (state : SplitState)
    (leftTrials rightTrials : Nat) :
    ProbComp ((α × SplitState) × List HashOutput × List HashOutput) := do
  let result ← (simulateQ (recorder leftKeep rightKeep) computation).run state
  let leftPad ← padding leftTrials
  let rightPad ← padding rightTrials
  pure (result, leftPad, rightPad)

theorem paddedFrom_bind {α β : Type} (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (computation : OracleComp OracleWorld α) (next : α → OracleComp OracleWorld β)
    (state : SplitState) (leftTrials rightTrials : Nat) :
    paddedFrom leftKeep rightKeep (computation >>= next) state leftTrials rightTrials =
      (simulateQ (recorder leftKeep rightKeep) computation).run state >>= fun step =>
        paddedFrom leftKeep rightKeep (next step.1) step.2 leftTrials rightTrials := by
  simp only [paddedFrom, simulateQ_bind, StateT.run_bind, bind_assoc]

/-! ## Both recordings only grow -/

theorem record_prefix {α : Type} (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (computation : OracleComp OracleWorld α) (state : SplitState) (result : α × SplitState)
    (hmem : result ∈ support ((simulateQ (recorder leftKeep rightKeep) computation).run state)) :
    state.2.1 <+: result.2.2.1 ∧ state.2.2 <+: result.2.2.2 := by
  classical
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [hmem]
    exact ⟨List.prefix_rfl, List.prefix_rfl⟩
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    obtain ⟨hleft, hright⟩ := ih step.1 step.2 result hrest
    refine ⟨List.IsPrefix.trans ?_ hleft, List.IsPrefix.trans ?_ hright⟩
    all_goals rcases queried with coin | input
    · have hsame : step.2 = state := by
        rw [recorder_run_inl, mem_support_bind_iff] at hstep
        obtain ⟨value, -, hpure⟩ := hstep
        rw [support_pure, Set.mem_singleton_iff] at hpure
        exact congrArg Prod.snd hpure
      rw [hsame]
    · rw [recorder_run_inr, mem_support_bind_iff] at hstep
      obtain ⟨inner, -, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [hpure]
      exact left_prefix_appended leftKeep rightKeep input state inner.1
    · have hsame : step.2 = state := by
        rw [recorder_run_inl, mem_support_bind_iff] at hstep
        obtain ⟨value, -, hpure⟩ := hstep
        rw [support_pure, Set.mem_singleton_iff] at hpure
        exact congrArg Prod.snd hpure
      rw [hsame]
    · rw [recorder_run_inr, mem_support_bind_iff] at hstep
      obtain ⟨inner, -, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [hpure]
      exact right_prefix_appended leftKeep rightKeep input state inner.1

theorem record_prefix_padded {α : Type} (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (computation : OracleComp OracleWorld α) (state : SplitState)
    (leftTrials rightTrials : Nat)
    (result : (α × SplitState) × List HashOutput × List HashOutput)
    (hmem : result ∈ support
      (paddedFrom leftKeep rightKeep computation state leftTrials rightTrials)) :
    state.2.1 <+: result.1.2.2.1 ∧ state.2.2 <+: result.1.2.2.2 := by
  rw [paddedFrom, mem_support_bind_iff] at hmem
  obtain ⟨inner, hinner, hrest⟩ := hmem
  rw [mem_support_bind_iff] at hrest
  obtain ⟨leftPad, -, hrest⟩ := hrest
  rw [mem_support_bind_iff] at hrest
  obtain ⟨rightPad, -, hpure⟩ := hrest
  rw [support_pure, Set.mem_singleton_iff] at hpure
  rw [hpure]
  exact record_prefix leftKeep rightKeep computation state inner hinner

/-! ## Two independent draws, two events

The run's own answers are what the induction charges; the two padding blocks are drawn
afterwards and independently, so the event they settle factors. -/

theorem prob_and_bind_le {α β γ : Type} (ma : ProbComp α) (mb : ProbComp β) (shape : α → β → γ)
    (event : γ → Prop) (left : α → Prop) (right : β → Prop) (a b : ℝ≥0∞)
    (hshape : ∀ x y, event (shape x y) → left x ∧ right y)
    (hleft : Pr[left | ma] ≤ a) (hright : Pr[right | mb] ≤ b) :
    Pr[event | ma >>= fun x => mb >>= fun y => (pure (shape x y) : ProbComp γ)] ≤ a * b := by
  classical
  rw [probEvent_bind_eq_tsum]
  have hinner : ∀ x : α,
      Pr[event | mb >>= fun y => (pure (shape x y) : ProbComp γ)] ≤
        (if left x then b else 0) := by
    intro x
    by_cases hx : left x
    · rw [if_pos hx, bind_pure_comp, probEvent_map]
      exact le_trans (probEvent_mono fun y _ hy => (hshape x y hy).2) hright
    · rw [if_neg hx]
      refine le_of_eq (probEvent_eq_zero fun value hvalue hevent => ?_)
      rw [mem_support_bind_iff] at hvalue
      obtain ⟨y, -, hpure⟩ := hvalue
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [hpure] at hevent
      exact hx (hshape x y hevent).1
  calc ∑' x : α, Pr[= x | ma] * Pr[event | mb >>= fun y => (pure (shape x y) : ProbComp γ)]
      ≤ ∑' x : α, Pr[= x | ma] * (if left x then b else 0) :=
        ENNReal.tsum_le_tsum fun x => mul_le_mul' le_rfl (hinner x)
    _ = ∑' x : α, (if left x then Pr[= x | ma] else 0) * b := by
        refine tsum_congr fun x => ?_
        by_cases hx : left x <;> simp [hx]
    _ = Pr[left | ma] * b := by rw [ENNReal.tsum_mul_right, ← probEvent_eq_tsum_ite]
    _ ≤ a * b := mul_le_mul' hleft le_rfl

/-- The letter a fresh recorded answer has to match is the next letter of the word. -/
theorem eq_head_of_prefix {start : List HashOutput} {answer head : HashOutput}
    {tail rest pad : List HashOutput} (hgrown : start ++ [answer] <+: rest)
    (hgoal : start ++ head :: tail <+: rest ++ pad) : answer = head := by
  have hgrownPad : start ++ [answer] <+: rest ++ pad :=
    hgrown.trans (List.prefix_append _ _)
  have hboth : start ++ [answer] <+: start ++ head :: tail :=
    List.prefix_of_prefix_length_le hgrownPad hgoal (by simp)
  have hinner := (List.prefix_append_right_inj start).mp hboth
  simpa using (List.cons_prefix_cons.mp hinner).1

/-! ## The joint invariant -/

set_option maxHeartbeats 1000000 in
/-- **The lazy-sampling invariant for two recordings at once.** Two words fixed in advance
extend the two starting recordings with probability at most `|HashOutput| ^ -(n₁ + n₂)`: every
letter of either word has to be matched by one fresh uniform answer, and no answer matches a
letter of both. -/
theorem prob_prefix_le {α : Type} (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (computation : OracleComp OracleWorld α) (leftTrials rightTrials : Nat) (state : SplitState)
    (leftTarget rightTarget : List HashOutput) :
    Pr[fun result : (α × SplitState) × List HashOutput × List HashOutput =>
        (answers state.2.1 ++ leftTarget <+: answers result.1.2.2.1 ++ result.2.1) ∧
          (answers state.2.2 ++ rightTarget <+: answers result.1.2.2.2 ++ result.2.2) |
      paddedFrom leftKeep rightKeep computation state leftTrials rightTrials] ≤
      (1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^
        (leftTarget.length + rightTarget.length) := by
  classical
  induction computation using OracleComp.inductionOn generalizing state leftTarget rightTarget
    with
  | pure value =>
    have hrun : paddedFrom leftKeep rightKeep (pure value) state leftTrials rightTrials =
        padding leftTrials >>= fun leftPad => padding rightTrials >>= fun rightPad =>
          (pure (((value, state), leftPad, rightPad)) : ProbComp _) := by
      rw [paddedFrom, simulateQ_pure, StateT.run_pure, pure_bind]
    rw [hrun, pow_add]
    refine prob_and_bind_le (padding leftTrials) (padding rightTrials)
      (fun leftPad rightPad => ((value, state), leftPad, rightPad)) _
      (fun leftPad => leftTarget <+: leftPad) (fun rightPad => rightTarget <+: rightPad)
      _ _ (fun leftPad rightPad hevent => ?_)
      (prob_padding_prefix_le leftTrials leftTarget)
      (prob_padding_prefix_le rightTrials rightTarget)
    exact ⟨(List.prefix_append_right_inj (answers state.2.1)).mp hevent.1,
      (List.prefix_append_right_inj (answers state.2.2)).mp hevent.2⟩
  | query_bind queried next ih =>
    rw [paddedFrom_bind, simulateQ_spec_query]
    rcases queried with coin | input
    · rw [recorder_run_inl, bind_assoc]
      simp only [pure_bind]
      rw [probEvent_bind_eq_tsum]
      calc ∑' value : OracleWorld.Range (Sum.inl coin),
            Pr[= value | ($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _)] *
              Pr[fun result : (α × SplitState) × List HashOutput × List HashOutput =>
                  (answers state.2.1 ++ leftTarget <+: answers result.1.2.2.1 ++ result.2.1) ∧
                    (answers state.2.2 ++ rightTarget <+:
                      answers result.1.2.2.2 ++ result.2.2) |
                paddedFrom leftKeep rightKeep (next value) state leftTrials rightTrials]
          ≤ ∑' value : OracleWorld.Range (Sum.inl coin),
              Pr[= value | ($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _)] *
                ((1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^
                  (leftTarget.length + rightTarget.length)) :=
            ENNReal.tsum_le_tsum fun value =>
              mul_le_mul' le_rfl (ih value state leftTarget rightTarget)
        _ = (∑' value : OracleWorld.Range (Sum.inl coin),
              Pr[= value | ($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _)]) *
                ((1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^
                  (leftTarget.length + rightTarget.length)) := ENNReal.tsum_mul_right
        _ ≤ 1 * ((1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^
              (leftTarget.length + rightTarget.length)) :=
            mul_le_mul' tsum_probOutput_le_one le_rfl
        _ = _ := one_mul _
    · rw [recorder_run_inr, bind_assoc]
      simp only [pure_bind]
      cases hcached : state.1 input with
      | some cached =>
        have hrom : (randomOracle input).run state.1 =
            (pure (cached, state.1) : ProbComp (HashOutput × QueryCache HashSpec)) := by
          rw [QueryImpl.withCaching_run_some _ hcached]
        have happended : appended leftKeep rightKeep input state cached = state.2 := by
          rw [appended, if_neg (by simp [hcached]), if_neg (by simp [hcached])]
        rw [hrom, pure_bind, happended]
        exact ih cached (state.1, state.2) leftTarget rightTarget
      | none =>
        have hrom : (randomOracle input).run state.1 =
            (fun answer => (answer, state.1.cacheQuery input answer)) <$>
              ($ᵗ HashOutput : ProbComp HashOutput) := by
          rw [QueryImpl.withCaching_run_none _ hcached]
          simp [uniformSampleImpl]
        rw [hrom, bind_map_left]
        by_cases hleft : leftKeep input state.1
        · have happended : ∀ answer : HashOutput,
              appended leftKeep rightKeep input state answer =
                (state.2.1 ++ [(input, answer)], state.2.2) :=
            fun answer => if_pos ⟨hcached, hleft⟩
          simp only [happended]
          cases leftTarget with
          | nil =>
            rw [probEvent_bind_eq_tsum]
            have hstep : ∀ answer : HashOutput,
                Pr[fun result : (α × SplitState) × List HashOutput × List HashOutput =>
                    (answers state.2.1 ++ [] <+: answers result.1.2.2.1 ++ result.2.1) ∧
                      (answers state.2.2 ++ rightTarget <+:
                        answers result.1.2.2.2 ++ result.2.2) |
                  paddedFrom leftKeep rightKeep (next answer)
                    (state.1.cacheQuery input answer,
                      state.2.1 ++ [(input, answer)], state.2.2) leftTrials rightTrials] ≤
                  (1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^
                    (([] : List HashOutput).length + rightTarget.length) := by
              intro answer
              refine le_trans (probEvent_mono fun result hresult hgoal => ?_)
                (ih answer (state.1.cacheQuery input answer,
                  state.2.1 ++ [(input, answer)], state.2.2) [] rightTarget)
              refine ⟨?_, hgoal.2⟩
              refine List.IsPrefix.trans ?_ (List.prefix_append _ _)
              simpa using answers_prefix (record_prefix_padded leftKeep rightKeep (next answer)
                (state.1.cacheQuery input answer, state.2.1 ++ [(input, answer)], state.2.2)
                leftTrials rightTrials result hresult).1
            calc ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                  Pr[fun result : (α × SplitState) × List HashOutput × List HashOutput =>
                      (answers state.2.1 ++ [] <+: answers result.1.2.2.1 ++ result.2.1) ∧
                        (answers state.2.2 ++ rightTarget <+:
                          answers result.1.2.2.2 ++ result.2.2) |
                    paddedFrom leftKeep rightKeep (next answer)
                      (state.1.cacheQuery input answer,
                        state.2.1 ++ [(input, answer)], state.2.2) leftTrials rightTrials]
                ≤ ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                    ((1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^
                      (([] : List HashOutput).length + rightTarget.length)) :=
                  ENNReal.tsum_le_tsum fun answer => mul_le_mul' le_rfl (hstep answer)
              _ = (∑' answer : HashOutput,
                    Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)]) *
                      ((1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^
                        (([] : List HashOutput).length + rightTarget.length)) :=
                  ENNReal.tsum_mul_right
              _ ≤ 1 * ((1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^
                    (([] : List HashOutput).length + rightTarget.length)) :=
                  mul_le_mul' tsum_probOutput_le_one le_rfl
              _ = _ := one_mul _
          | cons head tail =>
            rw [probEvent_bind_eq_tsum]
            have hstep : ∀ answer : HashOutput,
                Pr[fun result : (α × SplitState) × List HashOutput × List HashOutput =>
                    (answers state.2.1 ++ head :: tail <+:
                        answers result.1.2.2.1 ++ result.2.1) ∧
                      (answers state.2.2 ++ rightTarget <+:
                        answers result.1.2.2.2 ++ result.2.2) |
                  paddedFrom leftKeep rightKeep (next answer)
                    (state.1.cacheQuery input answer,
                      state.2.1 ++ [(input, answer)], state.2.2) leftTrials rightTrials] ≤
                  (if answer = head then
                    (1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^
                      (tail.length + rightTarget.length) else 0) := by
              intro answer
              by_cases hhead : answer = head
              · subst hhead
                rw [if_pos rfl]
                refine le_trans (le_of_eq ?_)
                  (ih answer (state.1.cacheQuery input answer,
                    state.2.1 ++ [(input, answer)], state.2.2) tail rightTarget)
                refine probEvent_congr' (fun result _ => ?_) rfl
                rw [answers_append, answers_singleton, List.append_assoc]
                rfl
              · rw [if_neg hhead]
                refine le_of_eq (probEvent_eq_zero fun result hresult hgoal => ?_)
                refine hhead (eq_head_of_prefix (pad := result.2.1) ?_ hgoal.1)
                simpa using answers_prefix (record_prefix_padded leftKeep rightKeep (next answer)
                  (state.1.cacheQuery input answer, state.2.1 ++ [(input, answer)], state.2.2)
                  leftTrials rightTrials result hresult).1
            calc ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                  Pr[fun result : (α × SplitState) × List HashOutput × List HashOutput =>
                      (answers state.2.1 ++ head :: tail <+:
                          answers result.1.2.2.1 ++ result.2.1) ∧
                        (answers state.2.2 ++ rightTarget <+:
                          answers result.1.2.2.2 ++ result.2.2) |
                    paddedFrom leftKeep rightKeep (next answer)
                      (state.1.cacheQuery input answer,
                        state.2.1 ++ [(input, answer)], state.2.2) leftTrials rightTrials]
                ≤ ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                    (if answer = head then
                      (1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^
                        (tail.length + rightTarget.length) else 0) :=
                  ENNReal.tsum_le_tsum fun answer => mul_le_mul' le_rfl (hstep answer)
              _ = Pr[= head | ($ᵗ HashOutput : ProbComp HashOutput)] *
                    (1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^
                      (tail.length + rightTarget.length) := by
                  rw [tsum_eq_single head (fun answer hanswer => by simp [hanswer])]
                  simp
              _ = _ := by
                  rw [probOutput_uniformSample, List.length_cons, one_div]
                  rw [show tail.length + 1 + rightTarget.length =
                    (tail.length + rightTarget.length) + 1 from by omega, pow_succ]
                  ring
        · by_cases hright : rightKeep input state.1
          · have happended : ∀ answer : HashOutput,
                appended leftKeep rightKeep input state answer =
                  (state.2.1, state.2.2 ++ [(input, answer)]) := by
              intro answer
              rw [appended, if_neg (fun hboth => hleft hboth.2), if_pos ⟨hcached, hright⟩]
            simp only [happended]
            cases rightTarget with
            | nil =>
              rw [probEvent_bind_eq_tsum]
              have hstep : ∀ answer : HashOutput,
                  Pr[fun result : (α × SplitState) × List HashOutput × List HashOutput =>
                      (answers state.2.1 ++ leftTarget <+:
                          answers result.1.2.2.1 ++ result.2.1) ∧
                        (answers state.2.2 ++ [] <+: answers result.1.2.2.2 ++ result.2.2) |
                    paddedFrom leftKeep rightKeep (next answer)
                      (state.1.cacheQuery input answer,
                        state.2.1, state.2.2 ++ [(input, answer)]) leftTrials rightTrials] ≤
                    (1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^
                      (leftTarget.length + ([] : List HashOutput).length) := by
                intro answer
                refine le_trans (probEvent_mono fun result hresult hgoal => ?_)
                  (ih answer (state.1.cacheQuery input answer,
                    state.2.1, state.2.2 ++ [(input, answer)]) leftTarget [])
                refine ⟨hgoal.1, ?_⟩
                refine List.IsPrefix.trans ?_ (List.prefix_append _ _)
                simpa using answers_prefix (record_prefix_padded leftKeep rightKeep (next answer)
                  (state.1.cacheQuery input answer, state.2.1, state.2.2 ++ [(input, answer)])
                  leftTrials rightTrials result hresult).2
              calc ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                    Pr[fun result : (α × SplitState) × List HashOutput × List HashOutput =>
                        (answers state.2.1 ++ leftTarget <+:
                            answers result.1.2.2.1 ++ result.2.1) ∧
                          (answers state.2.2 ++ [] <+: answers result.1.2.2.2 ++ result.2.2) |
                      paddedFrom leftKeep rightKeep (next answer)
                        (state.1.cacheQuery input answer,
                          state.2.1, state.2.2 ++ [(input, answer)]) leftTrials rightTrials]
                  ≤ ∑' answer : HashOutput,
                      Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                        ((1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^
                          (leftTarget.length + ([] : List HashOutput).length)) :=
                    ENNReal.tsum_le_tsum fun answer => mul_le_mul' le_rfl (hstep answer)
                _ = (∑' answer : HashOutput,
                      Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)]) *
                        ((1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^
                          (leftTarget.length + ([] : List HashOutput).length)) :=
                    ENNReal.tsum_mul_right
                _ ≤ 1 * ((1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^
                      (leftTarget.length + ([] : List HashOutput).length)) :=
                    mul_le_mul' tsum_probOutput_le_one le_rfl
                _ = _ := one_mul _
            | cons head tail =>
              rw [probEvent_bind_eq_tsum]
              have hstep : ∀ answer : HashOutput,
                  Pr[fun result : (α × SplitState) × List HashOutput × List HashOutput =>
                      (answers state.2.1 ++ leftTarget <+:
                          answers result.1.2.2.1 ++ result.2.1) ∧
                        (answers state.2.2 ++ head :: tail <+:
                          answers result.1.2.2.2 ++ result.2.2) |
                    paddedFrom leftKeep rightKeep (next answer)
                      (state.1.cacheQuery input answer,
                        state.2.1, state.2.2 ++ [(input, answer)]) leftTrials rightTrials] ≤
                    (if answer = head then
                      (1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^
                        (leftTarget.length + tail.length) else 0) := by
                intro answer
                by_cases hhead : answer = head
                · subst hhead
                  rw [if_pos rfl]
                  refine le_trans (le_of_eq ?_)
                    (ih answer (state.1.cacheQuery input answer,
                      state.2.1, state.2.2 ++ [(input, answer)]) leftTarget tail)
                  refine probEvent_congr' (fun result _ => ?_) rfl
                  rw [answers_append, answers_singleton, List.append_assoc]
                  rfl
                · rw [if_neg hhead]
                  refine le_of_eq (probEvent_eq_zero fun result hresult hgoal => ?_)
                  refine hhead (eq_head_of_prefix (pad := result.2.2) ?_ hgoal.2)
                  simpa using answers_prefix (record_prefix_padded leftKeep rightKeep
                    (next answer) (state.1.cacheQuery input answer,
                      state.2.1, state.2.2 ++ [(input, answer)])
                    leftTrials rightTrials result hresult).2
              calc ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                    Pr[fun result : (α × SplitState) × List HashOutput × List HashOutput =>
                        (answers state.2.1 ++ leftTarget <+:
                            answers result.1.2.2.1 ++ result.2.1) ∧
                          (answers state.2.2 ++ head :: tail <+:
                            answers result.1.2.2.2 ++ result.2.2) |
                      paddedFrom leftKeep rightKeep (next answer)
                        (state.1.cacheQuery input answer,
                          state.2.1, state.2.2 ++ [(input, answer)]) leftTrials rightTrials]
                  ≤ ∑' answer : HashOutput,
                      Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                      (if answer = head then
                        (1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^
                          (leftTarget.length + tail.length) else 0) :=
                    ENNReal.tsum_le_tsum fun answer => mul_le_mul' le_rfl (hstep answer)
                _ = Pr[= head | ($ᵗ HashOutput : ProbComp HashOutput)] *
                      (1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^
                        (leftTarget.length + tail.length) := by
                    rw [tsum_eq_single head (fun answer hanswer => by simp [hanswer])]
                    simp
                _ = _ := by
                    rw [probOutput_uniformSample, List.length_cons, one_div]
                    rw [show leftTarget.length + (tail.length + 1) =
                      (leftTarget.length + tail.length) + 1 from by omega, pow_succ]
                    ring
          · have happended : ∀ answer : HashOutput,
                appended leftKeep rightKeep input state answer = state.2 := by
              intro answer
              rw [appended, if_neg (fun hboth => hleft hboth.2),
                if_neg (fun hboth => hright hboth.2)]
            simp only [happended]
            rw [probEvent_bind_eq_tsum]
            calc ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                  Pr[fun result : (α × SplitState) × List HashOutput × List HashOutput =>
                      (answers state.2.1 ++ leftTarget <+:
                          answers result.1.2.2.1 ++ result.2.1) ∧
                        (answers state.2.2 ++ rightTarget <+:
                          answers result.1.2.2.2 ++ result.2.2) |
                    paddedFrom leftKeep rightKeep (next answer)
                      (state.1.cacheQuery input answer, state.2) leftTrials rightTrials]
                ≤ ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                    ((1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^
                      (leftTarget.length + rightTarget.length)) :=
                  ENNReal.tsum_le_tsum fun answer => mul_le_mul' le_rfl
                    (ih answer (state.1.cacheQuery input answer, state.2)
                      leftTarget rightTarget)
              _ = (∑' answer : HashOutput,
                    Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)]) *
                      ((1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^
                        (leftTarget.length + rightTarget.length)) := ENNReal.tsum_mul_right
              _ ≤ 1 * ((1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^
                    (leftTarget.length + rightTarget.length)) :=
                  mul_le_mul' tsum_probOutput_le_one le_rfl
              _ = _ := one_mul _

end SlhDsaSecurity.SplitPrefix
