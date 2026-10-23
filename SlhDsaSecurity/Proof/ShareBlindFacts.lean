import SlhDsaSecurity.Proof.ShareFlag
import SlhDsaSecurity.Proof.ShareSignCongr
import SlhDsaSecurity.Proof.BlindCharge
import SlhDsaSecurity.Proof.ServedDisclosure

/-!
# The blind game's step, without its flag, and the facts the charge reads

The flag of `ShareGame.handler` reads the table — a guess is a guess *at* a cell — so the
handler with its flag is not blind to anything. The flag is never read back by the handler,
though, so dropping it leaves a step (`blindStep`) whose law is the handler's with the flag
forgotten (`map_handler_run`), and that step is the one the charge is taken at.

The facts are those `BlindCharge.prob_sensitive_le` asks for, at a table drawn cell by cell
with the padding and `SK.prf` beside it:

* the step files its record at the served digests (`files_blindStep`);
* availability only grows (`available_mono`), and reads no cell but the always-available ones
  (`available_congr`);
* at a state where a cell is unavailable, the step does not read it (`blindStep_congr`): the
  open table reads only available cells, the key's root is always available, and the assembled
  signature reads only the cells its served digest releases (`ShareSignCongr.cellSig_congr`).
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.ShareBlindFacts

open Security CanonicalGraph ShareGame

/-! ## The step without its flag -/

open scoped Classical in
/-- **The blind game's step, flag dropped.** -/
noncomputable def blindStep (setup : Setup) : QueryImpl ShareSpec (StateT St ProbComp) :=
  fun queried state => match queried with
    | Sum.inl (Sum.inl (Sum.inl (Sum.inl coin))) => do
        let value ← ($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _)
        pure (value, state)
    | Sum.inl (Sum.inl (Sum.inl (Sum.inr input))) => do
        let step ← route false setup state input
        pure (step.1, { step.2 with record := state.record ++ [(input, state.served)] })
    | Sum.inl (Sum.inl (Sum.inr request)) =>
        match request.frame with
        | none => pure (none, state)
        | some framed => do
            let seed ← prfAt state framed
            let randomizer := Hashing.truncate seed.1
            let input := Hashing.messageInput randomizer setup.pk framed
            let digest ← route false setup seed.2 input
            pure (some (randomizer, digest.1),
              { digest.2 with
                  served := digest.2.served ++ [digest.1]
                  record := state.record ++ [(input, state.served)] })
    | Sum.inl (Sum.inr (request, drawn)) =>
        match drawn with
        | none => pure (none, { state with log := state.log ++ [⟨request, none⟩] })
        | some (randomizer, digest) =>
            if digest ∈ state.served then
              let bytes := (ShareSigner.cellSig setup.warm setup.sk randomizer digest).toBytes
              pure (some bytes, { state with log := state.log ++ [⟨request, some bytes⟩] })
            else pure (none, { state with log := state.log ++ [⟨request, none⟩] })
    | Sum.inr forgery =>
        pure ((), { state with
          record := state.record ++ (claimsOf setup state forgery).map fun candidate =>
            (candidate, state.served) })

/-- **Forgetting the flag of the blind handler is its flag-free step.** -/
theorem map_handler_run (setup : Setup) (queried : ShareSpec.Domain) (state : St) (flag : Bool) :
    (fun z => (z.1, z.2.1)) <$> ((handler false setup) queried).run (state, flag) =
      ((blindStep setup) queried).run state := by
  classical
  rcases queried with ((world | request) | ⟨request, drawn⟩) | forgery
  · rcases world with coin | input
    · simp [handler, blindStep, StateT.run]
    · simp [handler, blindStep, StateT.run]
  · cases hframe : request.frame with
    | none => simp [handler, blindStep, StateT.run, hframe]
    | some framed => simp [handler, blindStep, StateT.run, hframe]
  · cases drawn with
    | none => simp [handler, blindStep, StateT.run]
    | some pair =>
      obtain ⟨randomizer, digest⟩ := pair
      by_cases hserved : digest ∈ state.served
      · simp [handler, blindStep, StateT.run, hserved]
      · simp [handler, blindStep, StateT.run, hserved]
  · simp [handler, blindStep, StateT.run]

/-- **The blind run with its flag forgotten is the flag-free run.** -/
theorem map_run_handler (setup : Setup) {α : Type} (computation : OracleComp ShareSpec α)
    (start : St) (flag : Bool) :
    (fun z => (z.1, z.2.1)) <$> (simulateQ (handler false setup) computation).run (start, flag) =
      (simulateQ (blindStep setup) computation).run start :=
  BlindCharge.run_simulateQ_map_proj (handler false setup) (blindStep setup) Prod.fst
    (fun queried p => map_handler_run setup queried p.1 p.2) computation (start, flag)

/-! ## The step files its record -/

theorem files_blindStep (setup : Setup) :
    BlindCharge.Files St.record St.served (blindStep setup) := by
  intro queried state z hz
  rw [← map_handler_run setup queried state false, support_map] at hz
  obtain ⟨w, hw, hzw⟩ := hz
  obtain ⟨inputs, hrecord, -, -⟩ := ShareFlag.step_shape false setup queried (state, false) w hw
  refine ⟨inputs, ?_⟩
  rw [← hzw]
  exact hrecord

theorem served_prefix (setup : Setup) (queried : ShareSpec.Domain) (state : St)
    (z : ShareSpec.Range queried × St) (hz : z ∈ support (((blindStep setup) queried).run state)) :
    state.served <+: z.2.served := by
  rw [← map_handler_run setup queried state false, support_map] at hz
  obtain ⟨w, hw, hzw⟩ := hz
  rw [← hzw]
  obtain ⟨_, _, hprefix, _⟩ := ShareFlag.step_shape false setup queried (state, false) w hw
  exact hprefix

/-! ## Availability -/

/-- **Availability only grows with the served digests.** -/
theorem available_mono (setup : Setup) {served served' : List HashOutput}
    (hsub : ∀ digest ∈ served, digest ∈ served') (node : Node)
    (havailable : available setup served node) : available setup served' node := by
  classical
  refine ServedDisclosure.available_mono_signed _ (fun key index hindex => ?_) node havailable
  simp only [disclosed, Finset.mem_filter, Finset.mem_univ, true_and] at hindex ⊢
  obtain ⟨digest, hdigest, hrest⟩ := hindex
  exact ⟨digest, hsub digest hdigest, hrest⟩

/-- Availability is closed under the structure. -/
theorem available_closed (setup : Setup) (served : List HashOutput) (parent : StructuralNode)
    (hchildren : ∀ child ∈ parent.children, available setup served child) :
    available setup served (.structural parent) :=
  available_of_children_available _ _ hchildren

/-- An unavailable cell is not always available. -/
theorem not_alwaysAvailable_of_unavailable (setup : Setup) (served : List HashOutput)
    (index : Node) (hindex : ¬ available setup served index) : ¬ AlwaysAvailable index :=
  fun halways => hindex (available_of_alwaysAvailable _ _
    (ShareCells.revealedOf_le setup.table.1) halways)

/-! ## A setup drawn cell by cell -/

/-- The setup at a public seed, a cell table, and `SK.prf` with the padding. -/
def setupOf (publicSeed : Digest) (cells : Cells) (aux : Digest × Padding) : Setup :=
  ⟨aux.1, publicSeed, (cells, aux.2)⟩

/-- **The availability reads only always-available cells.** -/
theorem available_congr (publicSeed : Digest) (cells other : Cells) (aux : Digest × Padding)
    (hagree : ∀ node, AlwaysAvailable node → cells node = other node) :
    available (setupOf publicSeed cells aux) = available (setupOf publicSeed other aux) := by
  funext served node
  show Available (ShareCells.revealedOf cells) (disclosed served) node =
    Available (ShareCells.revealedOf other) (disclosed served) node
  rw [ShareCells.revealedOf_congr cells other hagree]

/-- Agreement off a cell that is not always available is agreement at every always-available
cell. -/
theorem agree_alwaysAvailable (index : Node) (hindex : ¬ AlwaysAvailable index)
    (cells other : Cells) (hagree : BlindCharge.AgreeOff index cells other) :
    ∀ node, AlwaysAvailable node → cells node = other node :=
  fun node hnode => hagree node fun heq => hindex (heq ▸ hnode)

theorem topRoot_alwaysAvailable : AlwaysAvailable (.structural topRoot) := True.intro

/-- The public key reads only the root, which is always available. -/
theorem pk_congr (publicSeed : Digest) (index : Node) (hindex : ¬ AlwaysAvailable index)
    (cells other : Cells) (aux : Digest × Padding) (hagree : BlindCharge.AgreeOff index cells other) :
    (setupOf publicSeed cells aux).pk = (setupOf publicSeed other aux).pk := by
  show (⟨publicSeed, cells (.structural topRoot)⟩ : PublicKey) =
    ⟨publicSeed, other (.structural topRoot)⟩
  rw [agree_alwaysAvailable index hindex cells other hagree _ topRoot_alwaysAvailable]

/-- **The open table reads only available cells.** -/
theorem openAt_congr (publicSeed : Digest) (index : Node) (cells other : Cells)
    (aux : Digest × Padding) (hagree : BlindCharge.AgreeOff index cells other)
    (served : List HashOutput) (hindex : ¬ available (setupOf publicSeed cells aux) served index) :
    openAt (setupOf publicSeed cells aux) served = openAt (setupOf publicSeed other aux) served := by
  have hnot := not_alwaysAvailable_of_unavailable _ served index hindex
  show OpenCache.openCache publicSeed (available (setupOf publicSeed cells aux) served)
      (cells, aux.2) =
    OpenCache.openCache publicSeed (available (setupOf publicSeed other aux) served) (other, aux.2)
  rw [← available_congr publicSeed cells other aux
    (agree_alwaysAvailable index hnot cells other hagree)]
  exact OpenCache.openCache_congr_of_agreeOff publicSeed _
    (available_closed (setupOf publicSeed cells aux) served) index hindex _ _
    ⟨hagree, fun _ _ => rfl⟩

/-- The open entries the claims are read off. -/
theorem visible_congr (publicSeed : Digest) (index : Node) (cells other : Cells)
    (aux : Digest × Padding) (hagree : BlindCharge.AgreeOff index cells other) (state : St)
    (hindex : ¬ available (setupOf publicSeed cells aux) state.served index) :
    visible (setupOf publicSeed cells aux) state = visible (setupOf publicSeed other aux) state := by
  unfold visible
  rw [openAt_congr publicSeed index cells other aux hagree state.served hindex]

/-- **The step reads no cell that is unavailable where it starts.** -/
theorem blindStep_congr (publicSeed : Digest) (index : Node) (cells other : Cells)
    (aux : Digest × Padding) (hagree : BlindCharge.AgreeOff index cells other)
    (queried : ShareSpec.Domain) (state : St)
    (hindex : ¬ available (setupOf publicSeed cells aux) state.served index) :
    𝒟[((blindStep (setupOf publicSeed cells aux)) queried).run state] =
      𝒟[((blindStep (setupOf publicSeed other aux)) queried).run state] := by
  classical
  have hnot := not_alwaysAvailable_of_unavailable _ state.served index hindex
  have hpk := pk_congr publicSeed index hnot cells other aux hagree
  have hroute : ∀ (st : St) (input : Bytes), st.served = state.served →
      route false (setupOf publicSeed cells aux) st input =
        route false (setupOf publicSeed other aux) st input := by
    intro st input hst
    unfold route
    rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, hst,
      openAt_congr publicSeed index cells other aux hagree state.served hindex]
    rfl
  rcases queried with ((world | request) | ⟨request, drawn⟩) | forgery
  · rcases world with coin | input
    · rfl
    · show 𝒟[(do
          let step ← route false (setupOf publicSeed cells aux) state input
          pure (step.1, { step.2 with record := state.record ++ [(input, state.served)] }))] =
        𝒟[(do
          let step ← route false (setupOf publicSeed other aux) state input
          pure (step.1, { step.2 with record := state.record ++ [(input, state.served)] }))]
      rw [hroute state input rfl]
  · cases hframe : request.frame with
    | none => simp [blindStep, StateT.run, hframe]
    | some framed =>
      simp only [blindStep, StateT.run, hframe, hpk]
      refine CapComp.evalDist_bind_congr_support _ _ _ fun seed hseed => ?_
      obtain ⟨hserved, -, -⟩ := ShareFlag.prfAt_mem_support state framed seed hseed
      rw [hroute seed.2 _ hserved]
  · cases drawn with
    | none => rfl
    | some pair =>
      obtain ⟨randomizer, digest⟩ := pair
      by_cases hserved : digest ∈ state.served
      · have hsig : ShareSigner.cellSig (setupOf publicSeed cells aux).warm
            (setupOf publicSeed cells aux).sk randomizer digest =
          ShareSigner.cellSig (setupOf publicSeed other aux).warm
            (setupOf publicSeed other aux).sk randomizer digest := by
          refine ShareSignCongr.cellSig_congr publicSeed aux.1 aux.1 (cells, aux.2)
            (other, aux.2) (disclosed state.served) (fun node hnode => ?_) randomizer digest
            (fun tree => ?_)
          · exact hagree node fun heq => hindex (heq ▸ hnode)
          · simp only [disclosed, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨digest, hserved, rfl, tree, Fin.ext rfl⟩
        simp only [blindStep, StateT.run, if_pos hserved, hsig]
      · simp only [blindStep, StateT.run, if_neg hserved]
  · have hclaims : claimsOf (setupOf publicSeed cells aux) state forgery =
        claimsOf (setupOf publicSeed other aux) state forgery := by
      unfold claimsOf
      rw [visible_congr publicSeed index cells other aux hagree state hindex, hpk]
      rfl
    simp only [blindStep, StateT.run, hclaims]

end SlhDsaSecurity.ShareBlindFacts
