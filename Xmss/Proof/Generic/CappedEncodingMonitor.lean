import Xmss.Proof.Generic.CappedEncodingRejection

open OracleComp ENNReal

namespace Xmss.Generic.CappedEncodingMonitor

variable [Code]

set_option maxRecDepth 100000

noncomputable def State.pendingRisk
    (state : EncodingMonitor.State) : ℝ≥0∞ :=
  (state.pendingCount : ℝ≥0∞) *
    (Code.validDigests.card : ℝ≥0∞)⁻¹

theorem State.pendingRisk_empty :
    State.pendingRisk EncodingMonitor.State.empty = 0 := by
  unfold State.pendingRisk
  rw [EncodingMonitor.State.pendingCount_empty, Nat.cast_zero, zero_mul]

theorem State.pendingRisk_install_add
    (state : EncodingMonitor.State) (leafIndex : LeafIndex) (digest : Digest) :
    State.pendingRisk (state.install leafIndex digest) +
        (state.pending leafIndex).card *
          (Code.validDigests.card : ℝ≥0∞)⁻¹ =
      State.pendingRisk state := by
  unfold State.pendingRisk
  rw [← add_mul, ← Nat.cast_add,
    EncodingMonitor.State.pendingCount_install_add]

theorem State.pendingRisk_addPending_le
    (state : EncodingMonitor.State) (leafIndex : LeafIndex) (digest : Digest) :
    State.pendingRisk (state.addPending leafIndex digest) ≤
      State.pendingRisk state +
        (Code.validDigests.card : ℝ≥0∞)⁻¹ := by
  unfold State.pendingRisk
  calc
    ((state.addPending leafIndex digest).pendingCount : ℝ≥0∞) *
        (Code.validDigests.card : ℝ≥0∞)⁻¹ ≤
      ((state.pendingCount + 1 : Nat) : ℝ≥0∞) *
        (Code.validDigests.card : ℝ≥0∞)⁻¹ := by
          gcongr
          exact_mod_cast state.pendingCount_addPending_le leafIndex digest
    _ = (state.pendingCount : ℝ≥0∞) *
          (Code.validDigests.card : ℝ≥0∞)⁻¹ +
        (Code.validDigests.card : ℝ≥0∞)⁻¹ := by
          push_cast
          rw [add_mul, one_mul]

omit [Code] in
theorem uniformDigest_if_eq_probability_le
    (target : Digest) (resume : Digest → ProbComp Bool) (ε : ℝ≥0∞)
    (hresume : ∀ digest, digest ≠ target →
      Pr[(· = true) | resume digest] ≤ ε) :
    Pr[(· = true) | do
      let digest ← $ᵗ Digest
      if digest = target then pure true else resume digest] ≤
      (Fintype.card Digest : ℝ≥0∞)⁻¹ + ε := by
  refine (probEvent_bind_le_probEvent_add
    (p := fun digest : Digest => digest = target) (ε := ε) ?_).trans ?_
  · intro digest _hdigest hmiss
    simpa [hmiss] using hresume digest hmiss
  · rw [probEvent_eq_eq_probOutput, probOutput_uniformSample]

theorem uniformDigest_valid_bonus_sum_eq :
    ∑ digest : Digest,
        Pr[= digest | $ᵗ Digest] *
          (if Code.ValidDigest digest then
            (Code.validDigests.card : ℝ≥0∞)⁻¹ else 0) =
      (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  simp_rw [probOutput_uniformSample]
  simp_rw [mul_ite, mul_zero]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul]
  change (Code.validDigests.card : ℝ≥0∞) *
      ((Fintype.card Digest : ℝ≥0∞)⁻¹ *
        (Code.validDigests.card : ℝ≥0∞)⁻¹) = _
  calc
    _ = (Fintype.card Digest : ℝ≥0∞)⁻¹ *
        ((Code.validDigests.card : ℝ≥0∞) *
          (Code.validDigests.card : ℝ≥0∞)⁻¹) := by ac_rfl
    _ = (Fintype.card Digest : ℝ≥0∞)⁻¹ * 1 := by
      rw [ENNReal.mul_inv_cancel]
      · exact_mod_cast Nat.ne_of_gt Code.validDigests_card_pos
      · exact ENNReal.natCast_ne_top _
    _ = _ := mul_one _

omit [Code] in
theorem uniformDigest_mem_bonus_sum_eq (targets : Finset Digest) :
    ∑ digest : Digest,
        Pr[= digest | $ᵗ Digest] *
          (if digest ∈ targets then 1 else 0) =
      (targets.card : ℝ≥0∞) *
        (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  simp_rw [probOutput_uniformSample]
  simp_rw [mul_ite, mul_one, mul_zero]
  have hfilter : Finset.univ.filter (fun digest : Digest => digest ∈ targets) =
      targets := by
    ext digest
    simp
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul, hfilter]

theorem uniformDigest_valid_scaled_bonus_sum_eq (scale : Nat) :
    ∑ digest : Digest,
        Pr[= digest | $ᵗ Digest] *
          (if Code.ValidDigest digest then
            (scale : ℝ≥0∞) *
              (Code.validDigests.card : ℝ≥0∞)⁻¹ else 0) =
      (scale : ℝ≥0∞) *
        (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  calc
    _ = (scale : ℝ≥0∞) *
        (∑ digest : Digest,
          Pr[= digest | $ᵗ Digest] *
            (if Code.ValidDigest digest then
              (Code.validDigests.card : ℝ≥0∞)⁻¹ else 0)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro digest _hdigest
          by_cases hvalid : Code.ValidDigest digest
          · simp only [hvalid, ↓reduceIte]
            ac_rfl
          · simp only [hvalid, ↓reduceIte, mul_zero]
    _ = _ := by rw [uniformDigest_valid_bonus_sum_eq]

theorem uniformDigest_sign_bonus_sum_le (targets : Finset Digest) :
    ∑ digest : Digest,
        Pr[= digest | $ᵗ Digest] *
          (if Code.ValidDigest digest then
            if digest ∈ targets then 1 else 0
          else
            (targets.card : ℝ≥0∞) *
              (Code.validDigests.card : ℝ≥0∞)⁻¹) ≤
      (targets.card : ℝ≥0∞) *
        (Code.validDigests.card : ℝ≥0∞)⁻¹ := by
  let removed := (targets.card : ℝ≥0∞) *
    (Code.validDigests.card : ℝ≥0∞)⁻¹
  calc
    _ ≤ ∑ digest : Digest,
        Pr[= digest | $ᵗ Digest] *
          ((if digest ∈ targets then 1 else 0) +
            if Code.ValidDigest digest then 0 else removed) := by
          apply Finset.sum_le_sum
          intro digest _hdigest
          apply mul_le_mul_right
          by_cases hvalid : Code.ValidDigest digest
          · by_cases hmem : digest ∈ targets <;>
              simp only [hvalid, hmem, ↓reduceIte, add_zero, le_refl]
          · by_cases hmem : digest ∈ targets
            · simp only [hvalid, hmem, ↓reduceIte]
              exact le_add_left le_rfl
            · simp only [hvalid, hmem, ↓reduceIte, zero_add]
              exact le_rfl
    _ = (∑ digest : Digest,
          Pr[= digest | $ᵗ Digest] *
            (if digest ∈ targets then 1 else 0)) +
        ∑ digest : Digest,
          Pr[= digest | $ᵗ Digest] *
            (if Code.ValidDigest digest then 0 else removed) := by
              simp_rw [mul_add]
              rw [Finset.sum_add_distrib]
    _ = (∑ digest : Digest,
          Pr[= digest | $ᵗ Digest] *
            (if Code.ValidDigest digest then removed else 0)) +
        ∑ digest : Digest,
          Pr[= digest | $ᵗ Digest] *
            (if Code.ValidDigest digest then 0 else removed) := by
              have hfirst :
                ∑ digest : Digest,
                    Pr[= digest | $ᵗ Digest] *
                      (if digest ∈ targets then 1 else 0) =
                  ∑ digest : Digest,
                    Pr[= digest | $ᵗ Digest] *
                      (if Code.ValidDigest digest then removed else 0) := by
                calc
                  _ = (targets.card : ℝ≥0∞) *
                        (Fintype.card Digest : ℝ≥0∞)⁻¹ :=
                    uniformDigest_mem_bonus_sum_eq targets
                  _ = _ := by
                    dsimp only [removed]
                    exact (uniformDigest_valid_scaled_bonus_sum_eq targets.card).symm
              rw [hfirst]
    _ = ∑ digest : Digest,
        Pr[= digest | $ᵗ Digest] * removed := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro digest _hdigest
          by_cases hvalid : Code.ValidDigest digest <;> simp [hvalid]
    _ = removed := by
          rw [← Finset.sum_mul]
          have hmass : ∑ digest : Digest, Pr[= digest | $ᵗ Digest] = 1 :=
            sum_probOutput_eq_one (mx := ($ᵗ Digest)) (by simp)
          rw [hmass, one_mul]

noncomputable def applyUniformSignAttemptMonitor
    (leafIndex : LeafIndex)
    (resume : Digest → EncodingMonitor.State → ProbComp Bool)
    (state : EncodingMonitor.State) : ProbComp Bool := do
  let digest ← $ᵗ Digest
  if Code.ValidDigest digest then
    match state.signed leafIndex with
    | some _ => pure false
    | none =>
        if digest ∈ state.pending leafIndex then pure true
        else resume digest (state.install leafIndex digest)
  else resume digest state

theorem applyUniformSignAttemptMonitor_true_probability_le
    (leafIndex : LeafIndex)
    (resume : Digest → EncodingMonitor.State → ProbComp Bool)
    (state : EncodingMonitor.State) (fuel : Nat)
    (hresume : ∀ digest nextState,
      Pr[(· = true) | resume digest nextState] ≤
        (fuel : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ +
          State.pendingRisk nextState) :
    Pr[(· = true) | applyUniformSignAttemptMonitor leafIndex resume state] ≤
      (fuel : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ +
        State.pendingRisk state := by
  cases hsigned : state.signed leafIndex with
  | some target =>
      unfold applyUniformSignAttemptMonitor
      rw [probEvent_bind_eq_tsum, tsum_fintype]
      calc
        _ ≤ ∑ digest : Digest,
            Pr[= digest | $ᵗ Digest] *
              ((fuel : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ +
                State.pendingRisk state) := by
                  apply Finset.sum_le_sum
                  intro digest _hdigest
                  apply mul_le_mul_right
                  by_cases hvalid : Code.ValidDigest digest
                  · simp [hvalid, hsigned]
                  · simpa [hvalid] using hresume digest state
        _ = _ := by
              rw [← Finset.sum_mul]
              have hmass : ∑ digest : Digest, Pr[= digest | $ᵗ Digest] = 1 :=
                sum_probOutput_eq_one (mx := ($ᵗ Digest)) (by simp)
              rw [hmass, one_mul]
  | none =>
      let base := (fuel : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹
      let remaining := State.pendingRisk (state.install leafIndex 0)
      let removed := ((state.pending leafIndex).card : ℝ≥0∞) *
        (Code.validDigests.card : ℝ≥0∞)⁻¹
      have hrisk : remaining + removed = State.pendingRisk state := by
        exact State.pendingRisk_install_add state leafIndex 0
      unfold applyUniformSignAttemptMonitor
      rw [probEvent_bind_eq_tsum, tsum_fintype]
      calc
        _ ≤ ∑ digest : Digest,
            Pr[= digest | $ᵗ Digest] *
              (base + remaining +
                if Code.ValidDigest digest then
                  if digest ∈ state.pending leafIndex then 1 else 0
                else removed) := by
                  apply Finset.sum_le_sum
                  intro digest _hdigest
                  apply mul_le_mul_right
                  by_cases hvalid : Code.ValidDigest digest
                  · simp only [hvalid, ↓reduceIte, hsigned]
                    by_cases hmem : digest ∈ state.pending leafIndex
                    · simp [hmem]
                    · simp only [hmem, ↓reduceIte, add_zero]
                      have hriskEq :
                          State.pendingRisk (state.install leafIndex digest) = remaining := by
                        unfold remaining State.pendingRisk
                        rw [EncodingMonitor.State.pendingCount_install_eq state leafIndex digest 0]
                      simpa [base, hriskEq] using
                        hresume digest (state.install leafIndex digest)
                  · simp only [hvalid, ↓reduceIte]
                    calc
                      Pr[(· = true) | resume digest state] ≤
                          base + State.pendingRisk state := by
                            simpa [base] using hresume digest state
                      _ = base + remaining + removed := by rw [← hrisk]; ac_rfl
        _ = (base + remaining) +
            ∑ digest : Digest,
              Pr[= digest | $ᵗ Digest] *
                (if Code.ValidDigest digest then
                  if digest ∈ state.pending leafIndex then 1 else 0
                else removed) := by
                  rw [show (∑ digest : Digest,
                      Pr[= digest | $ᵗ Digest] *
                        (base + remaining +
                          (if Code.ValidDigest digest then
                            if digest ∈ state.pending leafIndex then 1 else 0
                          else removed))) =
                      (∑ digest : Digest,
                        Pr[= digest | $ᵗ Digest] * (base + remaining)) +
                      ∑ digest : Digest,
                        Pr[= digest | $ᵗ Digest] *
                          (if Code.ValidDigest digest then
                            if digest ∈ state.pending leafIndex then 1 else 0
                          else removed) by
                            rw [← Finset.sum_add_distrib]
                            apply Finset.sum_congr rfl
                            intro digest _hdigest
                            rw [mul_add]]
                  rw [← Finset.sum_mul]
                  have hmass : ∑ digest : Digest, Pr[= digest | $ᵗ Digest] = 1 :=
                    sum_probOutput_eq_one (mx := ($ᵗ Digest)) (by simp)
                  rw [hmass, one_mul]
        _ ≤ (base + remaining) + removed := by
              gcongr
              exact uniformDigest_sign_bonus_sum_le (state.pending leafIndex)
        _ = base + State.pendingRisk state := by rw [← hrisk]; ac_rfl

noncomputable def applyUniformQueryMonitor
    (leafIndex : LeafIndex)
    (resume : Digest → EncodingMonitor.State → ProbComp Bool)
    (state : EncodingMonitor.State) : ProbComp Bool := do
  let digest ← $ᵗ Digest
  match state.signed leafIndex with
  | some target =>
      if digest = target then pure true else resume digest state
  | none =>
      if Code.ValidDigest digest then
        resume digest (state.addPending leafIndex digest)
      else resume digest state

theorem applyUniformQueryMonitor_true_probability_le
    (leafIndex : LeafIndex)
    (resume : Digest → EncodingMonitor.State → ProbComp Bool)
    (state : EncodingMonitor.State) (fuel : Nat)
    (hresume : ∀ digest nextState,
      Pr[(· = true) | resume digest nextState] ≤
        (fuel : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ +
          State.pendingRisk nextState) :
    Pr[(· = true) | applyUniformQueryMonitor leafIndex resume state] ≤
      (fuel.succ : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ +
        State.pendingRisk state := by
  cases hsigned : state.signed leafIndex with
  | some target =>
      unfold applyUniformQueryMonitor
      rw [hsigned]
      refine (uniformDigest_if_eq_probability_le target
        (fun digest => resume digest state)
        ((fuel : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ +
          State.pendingRisk state) ?_).trans_eq ?_
      · intro digest _hne
        exact hresume digest state
      · rw [Nat.cast_succ, add_mul, one_mul]
        ac_rfl
  | none =>
      unfold applyUniformQueryMonitor
      rw [hsigned, probEvent_bind_eq_tsum, tsum_fintype]
      calc
        ∑ digest : Digest,
            Pr[= digest | $ᵗ Digest] *
              Pr[(· = true) |
                if Code.ValidDigest digest then
                  resume digest (state.addPending leafIndex digest)
                else resume digest state] ≤
          ∑ digest : Digest,
            Pr[= digest | $ᵗ Digest] *
              ((fuel : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ +
                State.pendingRisk state +
                if Code.ValidDigest digest then
                  (Code.validDigests.card : ℝ≥0∞)⁻¹ else 0) := by
                    apply Finset.sum_le_sum
                    intro digest _hdigest
                    apply mul_le_mul_right
                    by_cases hvalid : Code.ValidDigest digest
                    · simp only [hvalid, ↓reduceIte]
                      calc
                        Pr[(· = true) |
                            resume digest (state.addPending leafIndex digest)] ≤
                          (fuel : ℝ≥0∞) *
                              (Fintype.card Digest : ℝ≥0∞)⁻¹ +
                            State.pendingRisk (state.addPending leafIndex digest) :=
                              hresume digest (state.addPending leafIndex digest)
                        _ ≤ (fuel : ℝ≥0∞) *
                              (Fintype.card Digest : ℝ≥0∞)⁻¹ +
                            (State.pendingRisk state +
                              (Code.validDigests.card : ℝ≥0∞)⁻¹) := by
                                gcongr
                                exact State.pendingRisk_addPending_le state leafIndex digest
                        _ = _ := by ac_rfl
                    · simpa only [hvalid, ↓reduceIte, add_zero] using
                        hresume digest state
        _ = ((fuel : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ +
              State.pendingRisk state) +
            (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
              simp_rw [mul_add]
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
                ← Finset.sum_mul, ← Finset.sum_mul]
              have hmass : ∑ digest : Digest, Pr[= digest | $ᵗ Digest] = 1 :=
                sum_probOutput_eq_one (mx := ($ᵗ Digest)) (by simp)
              rw [hmass, one_mul, uniformDigest_valid_bonus_sum_eq, one_mul]
        _ = (fuel.succ : ℝ≥0∞) *
              (Fintype.card Digest : ℝ≥0∞)⁻¹ +
            State.pendingRisk state := by
              rw [Nat.cast_succ, add_mul, one_mul]
              ac_rfl

noncomputable def State.applyObserved
    (state : EncodingMonitor.State) : EncodingMonitor.ObservedAction →
      Option (EncodingMonitor.State × Bool)
  | .query leafIndex output =>
      let digest := output
      match state.signed leafIndex with
      | some target => some (state, digest = target)
      | none =>
          if Code.ValidDigest digest then
            some (state.addPending leafIndex digest, false)
          else some (state, false)
  | .sign leafIndex output =>
      let digest := output
      if Code.ValidDigest digest then
        match state.signed leafIndex with
        | some _ => none
        | none => some (state.install leafIndex digest, digest ∈ state.pending leafIndex)
      else some (state, false)

theorem applyUniformQueryMonitor_eq_observed
    (leafIndex : LeafIndex)
    (resume : Digest → EncodingMonitor.State → ProbComp Bool)
    (state : EncodingMonitor.State) :
    applyUniformQueryMonitor leafIndex resume state =
      uniformHashOutput >>= fun output =>
        match State.applyObserved state (.query leafIndex output) with
        | none => pure false
        | some (nextState, hit) =>
            if hit then pure true else resume output nextState := by
  unfold applyUniformQueryMonitor State.applyObserved uniformHashOutput
  apply bind_congr
  intro output
  cases hsigned : state.signed leafIndex with
  | some target =>
      by_cases heq : output = target <;>
        simp [hsigned, heq]
  | none =>
      by_cases hvalid : Code.ValidDigest (output) <;>
        simp [hsigned, hvalid]

theorem applyUniformSignAttemptMonitor_eq_observed
    (leafIndex : LeafIndex)
    (resume : Digest → EncodingMonitor.State → ProbComp Bool)
    (state : EncodingMonitor.State) :
    applyUniformSignAttemptMonitor leafIndex resume state =
      uniformHashOutput >>= fun output =>
        match State.applyObserved state (.sign leafIndex output) with
        | none => pure false
        | some (nextState, hit) =>
            if hit then pure true else resume output nextState := by
  unfold applyUniformSignAttemptMonitor State.applyObserved uniformHashOutput
  apply bind_congr
  intro output
  by_cases hvalid : Code.ValidDigest (output)
  · cases hsigned : state.signed leafIndex with
    | some target => simp [hvalid, hsigned]
    | none =>
        by_cases hmem : output ∈ state.pending leafIndex <;>
          simp [hvalid, hsigned, hmem]
  · simp [hvalid]

noncomputable def runObserved : EncodingMonitor.State →
    List EncodingMonitor.ObservedAction → Bool
  | _state, [] => false
  | state, action :: actions =>
      match State.applyObserved state action with
      | none => false
      | some (nextState, hit) => hit || runObserved nextState actions

def ActionValid : EncodingMonitor.ObservedAction → Prop
  | .query _ output => Code.ValidDigest (output)
  | .sign _ output => Code.ValidDigest (output)

noncomputable instance : DecidablePred ActionValid :=
  Classical.decPred _

noncomputable def validActions
    (actions : List EncodingMonitor.ObservedAction) :
    List EncodingMonitor.ObservedAction :=
  match actions with
  | [] => []
  | action :: tail =>
      if ActionValid action then action :: validActions tail
      else validActions tail

noncomputable def validObservedSignLeafIndices
    (actions : List EncodingMonitor.ObservedAction) : List LeafIndex :=
  EncodingMonitor.observedSignLeafIndices (validActions actions)

@[simp]
theorem validActions_append
    (left right : List EncodingMonitor.ObservedAction) :
    validActions (left ++ right) = validActions left ++ validActions right := by
  induction left with
  | nil => rfl
  | cons action left ih =>
      by_cases hvalid : ActionValid action <;>
        simp [validActions, hvalid, ih]

theorem validActions_append_two_valid
    (before middle after : List EncodingMonitor.ObservedAction)
    (first second : EncodingMonitor.ObservedAction)
    (hfirst : ActionValid first) (hsecond : ActionValid second) :
    validActions (before ++ [first] ++ middle ++ [second] ++ after) =
      validActions before ++ [first] ++ validActions middle ++ [second] ++
        validActions after := by
  simp [validActions, hfirst, hsecond]

@[simp]
theorem validObservedSignLeafIndices_append
    (left right : List EncodingMonitor.ObservedAction) :
    validObservedSignLeafIndices (left ++ right) =
      validObservedSignLeafIndices left ++ validObservedSignLeafIndices right := by
  simp [validObservedSignLeafIndices]

@[simp] theorem validObservedSignLeafIndices_singleton_query
    (leafIndex : LeafIndex) (output : Digest) :
    validObservedSignLeafIndices [.query leafIndex output] = [] := by
  by_cases hvalid : ActionValid (.query leafIndex output) <;>
    simp [validObservedSignLeafIndices, validActions, hvalid,
      EncodingMonitor.observedSignLeafIndices]

theorem validObservedSignLeafIndices_singleton_sign
    (leafIndex : LeafIndex) (output : Digest) :
    validObservedSignLeafIndices [.sign leafIndex output] =
      if ActionValid (.sign leafIndex output) then [leafIndex] else [] := by
  by_cases hvalid : ActionValid (.sign leafIndex output) <;>
    simp [validObservedSignLeafIndices, validActions, hvalid,
      EncodingMonitor.observedSignLeafIndices]

theorem validActions_sublist_of_sublist
    {left right : List EncodingMonitor.ObservedAction}
    (hsub : left.Sublist right) :
    (validActions left).Sublist (validActions right) := by
  induction hsub with
  | slnil => simp [validActions]
  | cons action hsub ih =>
      by_cases hvalid : ActionValid action
      · simpa [validActions, hvalid] using ih.cons action
      · simpa [validActions, hvalid] using ih
  | cons_cons action hsub ih =>
      by_cases hvalid : ActionValid action
      · simpa [validActions, hvalid] using ih.cons_cons action
      · simpa [validActions, hvalid] using ih

theorem validActions_sublist
    (actions : List EncodingMonitor.ObservedAction) :
    (validActions actions).Sublist actions := by
  induction actions with
  | nil => simp [validActions]
  | cons action actions ih =>
      by_cases hvalid : ActionValid action
      · simpa [validActions, hvalid] using ih.cons_cons action
      · simpa [validActions, hvalid] using ih.cons action

def State.Valid (state : EncodingMonitor.State) : Prop :=
  (∀ leafIndex digest, state.signed leafIndex = some digest →
    Code.ValidDigest digest) ∧
  ∀ leafIndex digest, digest ∈ state.pending leafIndex → Code.ValidDigest digest

theorem State.valid_empty : State.Valid EncodingMonitor.State.empty := by
  constructor <;> simp [EncodingMonitor.State.empty]

theorem State.Valid.addPending
    (hstate : State.Valid state) (leafIndex : LeafIndex) (digest : Digest)
    (hvalid : Code.ValidDigest digest) :
    State.Valid (state.addPending leafIndex digest) := by
  constructor
  · exact hstate.1
  · intro candidate value hmem
    by_cases heq : candidate = leafIndex
    · subst candidate
      simp [EncodingMonitor.State.addPending] at hmem
      exact hmem.elim (fun hvalue => hvalue ▸ hvalid) (hstate.2 leafIndex value)
    · apply hstate.2 candidate value
      simpa [EncodingMonitor.State.addPending, heq] using hmem

theorem State.Valid.install
    (hstate : State.Valid state) (leafIndex : LeafIndex) (digest : Digest)
    (hvalid : Code.ValidDigest digest) :
    State.Valid (state.install leafIndex digest) := by
  constructor
  · intro candidate value hsigned
    by_cases heq : candidate = leafIndex
    · subst candidate
      simp [EncodingMonitor.State.install] at hsigned
      subst value
      exact hvalid
    · exact hstate.1 candidate value (by
        simpa [EncodingMonitor.State.install, heq] using hsigned)
  · intro candidate value hmem
    by_cases heq : candidate = leafIndex
    · subst candidate
      simp [EncodingMonitor.State.install] at hmem
    · exact hstate.2 candidate value (by
        simpa [EncodingMonitor.State.install, heq] using hmem)

theorem State.applyObserved_eq_standard_of_valid
    (state : EncodingMonitor.State) (action : EncodingMonitor.ObservedAction)
    (hvalid : ActionValid action) :
    State.applyObserved state action =
      EncodingMonitor.State.applyObserved state action := by
  cases action with
  | query leafIndex output =>
      simp only [ActionValid] at hvalid
      simp [State.applyObserved, EncodingMonitor.State.applyObserved, hvalid]
      rfl
  | sign leafIndex output =>
      simp only [ActionValid] at hvalid
      simp [State.applyObserved, EncodingMonitor.State.applyObserved, hvalid]
      rfl

theorem State.applyObserved_eq_unchanged_of_invalid
    (state : EncodingMonitor.State) (action : EncodingMonitor.ObservedAction)
    (hstate : State.Valid state) (hinvalid : ¬ActionValid action) :
    State.applyObserved state action = some (state, false) := by
  cases action with
  | query leafIndex output =>
      simp only [ActionValid] at hinvalid
      cases hsigned : state.signed leafIndex with
      | none => simp [State.applyObserved, hsigned, hinvalid]
      | some target =>
          have htarget := hstate.1 leafIndex target hsigned
          have hne : output ≠ target := by
            intro heq
            exact hinvalid (heq ▸ htarget)
          simp [State.applyObserved, hsigned, hne]
  | sign leafIndex output =>
      simp only [ActionValid] at hinvalid
      simp [State.applyObserved, hinvalid]

theorem State.Valid.applyObserved
    (hstate : State.Valid state) (action : EncodingMonitor.ObservedAction)
    (hvalid : ActionValid action)
    (nextState : EncodingMonitor.State) (hit : Bool)
    (happly : State.applyObserved state action = some (nextState, hit)) :
    State.Valid nextState := by
  cases action with
  | query leafIndex output =>
      simp only [ActionValid] at hvalid
      cases hsigned : state.signed leafIndex with
      | some target =>
          simp [State.applyObserved, hsigned] at happly
          rcases happly with ⟨rfl, rfl⟩
          exact hstate
      | none =>
          simp [State.applyObserved, hsigned, hvalid] at happly
          rcases happly with ⟨rfl, rfl⟩
          exact hstate.addPending leafIndex (output) hvalid
  | sign leafIndex output =>
      simp only [ActionValid] at hvalid
      cases hsigned : state.signed leafIndex with
      | some target => simp [State.applyObserved, hsigned, hvalid] at happly
      | none =>
          simp [State.applyObserved, hsigned, hvalid] at happly
          rcases happly with ⟨rfl, rfl⟩
          exact hstate.install leafIndex (output) hvalid

theorem runObserved_eq_standard_validActions
    (state : EncodingMonitor.State)
    (actions : List EncodingMonitor.ObservedAction)
    (hstate : State.Valid state) :
    runObserved state actions =
      EncodingMonitor.runObserved state (validActions actions) := by
  induction actions generalizing state with
  | nil => rfl
  | cons action actions ih =>
      by_cases hvalid : ActionValid action
      · rw [runObserved, validActions, if_pos hvalid,
          EncodingMonitor.runObserved_cons]
        have heq := State.applyObserved_eq_standard_of_valid state action hvalid
        cases happly : State.applyObserved state action with
        | none =>
            have hstandard : EncodingMonitor.State.applyObserved state action = none :=
              heq.symm.trans happly
            simp [hstandard]
        | some result =>
            rcases result with ⟨nextState, hit⟩
            have hnext := hstate.applyObserved action hvalid nextState hit happly
            have hstandard : EncodingMonitor.State.applyObserved state action =
                some (nextState, hit) := heq.symm.trans happly
            simp [hstandard, ih nextState hnext]
      · rw [runObserved, validActions, if_neg hvalid]
        rw [State.applyObserved_eq_unchanged_of_invalid state action hstate hvalid]
        simp [ih state hstate]

theorem runObserved_empty_eq_true_mono_sublist
    {left right : List EncodingMonitor.ObservedAction}
    (hsub : left.Sublist right)
    (hnodup : (validObservedSignLeafIndices right).Nodup)
    (hhit : runObserved EncodingMonitor.State.empty left = true) :
    runObserved EncodingMonitor.State.empty right = true := by
  rw [runObserved_eq_standard_validActions _ _ State.valid_empty] at hhit ⊢
  exact EncodingMonitor.runObserved_empty_eq_true_mono_sublist
    (validActions_sublist_of_sublist hsub) hnodup hhit

end Xmss.Generic.CappedEncodingMonitor
