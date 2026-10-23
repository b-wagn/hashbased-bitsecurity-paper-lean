import SlhDsaSecurity.Proof.ShareBlindFacts
import SlhDsaSecurity.Proof.VerifyBound
import SlhDsaSecurity.Proof.BlockViews
import SlhDsaSecurity.Proof.Target127

/-!
# The blind game's bound

The flag of the blind game is a union of guesses, each charged `2 ^ -128`, against a record no
longer than `limit + 3929 + 259`:

* **the record's length** (`length_shareComp`): the capped adversary files at most `limit`
  entries (`CapComp.cost_capComp_le`, with `ShareFlag.reportsCost`), the verifier at most
  `3929` (`VerifyBound.isQueryBoundP_verify`), and the claims at most `259`;
* **the cell guesses**: an entry that is a sensitive probe guesses a cell the blind run has not
  read, `BlindCharge.prob_sensitive_le` with the facts of `ShareBlindFacts`;
* **the `SK.prf` guesses**: the blind run never reads `SK.prf`, so it may be drawn after the
  run, and an entry not prefixed by the public seed guesses it at most once.

The claims file nothing once the flag is up, so the charge is taken at the blind handler's
filing form (`ShareBlindFacts.filing`), which files them whatever the flag: its flag has the blind
game's law (`probEvent_flagGame_eq`) and its record bounds the same way
(`length_filing_shareComp`).

An entry locating a node is prefixed by the public seed, so the two kinds of guess are counted
against disjoint parts of the record and add to at most its length.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.ShareBound

open Security CanonicalGraph ShareGame ShareFlag ShareBlindFacts

/-! ## The record's length -/

/-- The game's handler, read at the verifier's oracles. -/
noncomputable def worldImpl (lenient : Bool) (setup : Setup) :
    QueryImpl OracleWorld (StateT (St × Bool) ProbComp) :=
  QueryImpl.compose (handler lenient setup) fun world =>
    (query (spec := ShareSpec) (worldQuery world) : OracleComp ShareSpec (OracleWorld.Range world))

theorem verifyShare_run (lenient : Bool) (setup : Setup) (pk : PublicKey) (forgery : Forgery)
    (p : St × Bool) :
    (simulateQ (handler lenient setup) (verifyShare pk forgery)).run p =
      (simulateQ (worldImpl lenient setup)
        (Scheme.verify (m := OracleComp OracleWorld) pk forgery.message forgery.signature)).run p := by
  rw [verifyShare, ← QueryImpl.simulateQ_compose]
  rfl

theorem length_world_step (lenient : Bool) (setup : Setup) (queried : OracleWorld.Domain)
    (p : St × Bool) (z : OracleWorld.Range queried × (St × Bool))
    (hz : z ∈ support (((worldImpl lenient setup) queried).run p)) :
    z.2.1.record.length = p.1.record.length + if VerifyBound.IsHash queried then 1 else 0 := by
  rcases queried with coin | input
  · simp only [worldImpl, QueryImpl.apply_compose, worldQuery] at hz
    have := length_step lenient setup (Sum.inl (Sum.inl (Sum.inl (Sum.inl coin)))) p z
      (by simp at hz; exact hz)
    simpa [added, VerifyBound.IsHash] using this
  · simp only [worldImpl, QueryImpl.apply_compose, worldQuery] at hz
    have := length_step lenient setup (Sum.inl (Sum.inl (Sum.inl (Sum.inr input)))) p z
      (by simp at hz; exact hz)
    simpa [added, VerifyBound.IsHash] using this

/-- **A run with at most `n` hash calls files at most `n` entries.** -/
theorem length_world_run (lenient : Bool) (setup : Setup) {β : Type}
    (oa : OracleComp OracleWorld β) :
    ∀ (n : Nat), IsQueryBoundP oa VerifyBound.IsHash n → ∀ (p : St × Bool),
      ∀ z ∈ support ((simulateQ (worldImpl lenient setup) oa).run p),
        z.2.1.record.length ≤ p.1.record.length + n := by
  induction oa using OracleComp.inductionOn with
  | pure value =>
    intro n _ p z hz
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
    exact Nat.le_add_right _ _
  | query_bind t next ih =>
    intro n hbound p z hz
    rw [isQueryBoundP_def, isQueryBound_query_bind_iff] at hbound
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨step, hstep, hrest⟩ := hz
    have hfirst := length_world_step lenient setup t p step hstep
    have hrestBound := ih step.1 _ (hbound.2 step.1) step.2 z hrest
    by_cases hhash : VerifyBound.IsHash t
    · have hpos : 0 < n := hbound.1.resolve_left (not_not.mpr hhash)
      rw [if_pos hhash] at hfirst hrestBound
      omega
    · rw [if_neg hhash] at hfirst hrestBound
      omega

/-- The claims file at most `259` entries. -/
theorem length_claimsOf_le (setup : Setup) (state : St) (forgery : Forgery) :
    (claimsOf setup state forgery).length ≤ 259 := by
  unfold claimsOf
  split
  · rw [@ClaimedProbes.length_claimedCandidatesOf (CacheReplay.replayQuery (visible setup state))]
  · simp

/-- **The claims step files at most `259` entries**: the candidates not already filed, and none
once the flag is up. -/
theorem length_claims_le (lenient : Bool) (setup : Setup) (forgery : Forgery) (p : St × Bool)
    (z : Unit × (St × Bool))
    (hz : z ∈ support (((handler lenient setup) (Sum.inr forgery)).run p)) :
    z.2.1.record.length ≤ p.1.record.length + 259 := by
  have hstep := length_step lenient setup (Sum.inr forgery) p z hz
  have hclaims := length_claimsOf_le setup p.1 forgery
  have hunfiled := length_unfiled_le p.1.record p.1.served (claimsOf setup p.1 forgery)
  simp only [added] at hstep
  split_ifs at hstep <;> omega

/-- A world query, at a handler that is the game's away from the claims. -/
theorem simulateQ_inl_query (impl : QueryImpl ShareSpec (StateT (St × Bool) ProbComp))
    (lenient : Bool) (setup : Setup)
    (hinl : ∀ queried, impl (Sum.inl queried) = handler lenient setup (Sum.inl queried))
    (queried : (OracleWorld + DrawSpec + AssembleSpec).Domain) :
    simulateQ impl (query (spec := ShareSpec) (Sum.inl queried) :
        OracleComp ShareSpec (ShareSpec.Range (Sum.inl queried))) =
      simulateQ (handler lenient setup) (query (spec := ShareSpec) (Sum.inl queried) :
        OracleComp ShareSpec (ShareSpec.Range (Sum.inl queried))) := by
  erw [simulateQ_spec_query, simulateQ_spec_query]
  exact hinl queried

/-- **Away from the claims, a handler that is the game's reads the adversary's oracles as the
game does.** -/
theorem compose_splitter_of (impl : QueryImpl ShareSpec (StateT (St × Bool) ProbComp))
    (lenient : Bool) (setup : Setup)
    (hinl : ∀ queried, impl (Sum.inl queried) = handler lenient setup (Sum.inl queried)) :
    QueryImpl.compose impl splitter = advImpl lenient setup := by
  funext queried
  rcases queried with world | request
  · exact simulateQ_inl_query impl lenient setup hinl _
  · simp only [advImpl, QueryImpl.apply_compose, splitter, simulateQ_bind]
    rw [simulateQ_inl_query impl lenient setup hinl]
    refine bind_congr fun drawn => ?_
    exact simulateQ_inl_query impl lenient setup hinl _

/-- The same at the verifier's oracles. -/
theorem compose_world_of (impl : QueryImpl ShareSpec (StateT (St × Bool) ProbComp))
    (lenient : Bool) (setup : Setup)
    (hinl : ∀ queried, impl (Sum.inl queried) = handler lenient setup (Sum.inl queried)) :
    QueryImpl.compose impl (fun world =>
      (query (spec := ShareSpec) (worldQuery world) :
        OracleComp ShareSpec (OracleWorld.Range world))) = worldImpl lenient setup := by
  funext world
  exact simulateQ_inl_query impl lenient setup hinl _

set_option maxHeartbeats 1000000 in
/-- **The record never holds more than `limit + 3929 + 259` entries**, at any handler that is
the game's away from the claims and whose claims file at most `259` entries. -/
theorem length_shareComp_of (impl : QueryImpl ShareSpec (StateT (St × Bool) ProbComp))
    (lenient : Bool) (setup : Setup)
    (hinl : ∀ queried, impl (Sum.inl queried) = handler lenient setup (Sum.inl queried))
    (hclaims : ∀ (forgery : Forgery) (p : St × Bool) (z : Unit × (St × Bool)),
      z ∈ support ((impl (Sum.inr forgery)).run p) →
        z.2.1.record.length ≤ p.1.record.length + 259)
    (adversary : Adversary) (limit : Nat) (pk : PublicKey) (flag : Bool) :
    ∀ z ∈ support ((simulateQ impl (shareComp adversary limit pk)).run (St.start, flag)),
      z.2.1.record.length ≤ limit + 3929 + 259 := by
  intro z hz
  unfold shareComp at hz
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨afterAdversary, hadversary, hz⟩ := hz
  rw [← QueryImpl.simulateQ_compose, compose_splitter_of impl lenient setup hinl] at hadversary
  have hcap := CapComp.cost_capComp_le (advImpl lenient setup) weight
    (fun state : St × Bool => state.1.record.length) (reportsCost lenient setup)
    fallbackForgery (adversary.main pk) limit (St.start, flag) afterAdversary hadversary
  simp only [St.start, List.length_nil, Nat.zero_add] at hcap
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨afterVerify, hverify, hz⟩ := hz
  rw [verifyShare, ← QueryImpl.simulateQ_compose, compose_world_of impl lenient setup hinl]
    at hverify
  have hverifyBound := length_world_run lenient setup _ VerifyBound.verifyLimit
    (VerifyBound.isQueryBoundP_verify pk afterAdversary.1.message afterAdversary.1.signature)
    afterAdversary.2 afterVerify hverify
  rw [VerifyBound.verifyLimit_eq] at hverifyBound
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨afterClaims, hclaimsRun, hz⟩ := hz
  have hclaimsStep := hclaims afterAdversary.1 afterVerify.2 afterClaims
    (by simp at hclaimsRun; exact hclaimsRun)
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  rw [hz]
  dsimp only
  omega

/-- **The record never holds more than `limit + 3929 + 259` entries.** -/
theorem length_shareComp (lenient : Bool) (setup : Setup) (adversary : Adversary) (limit : Nat)
    (pk : PublicKey) (flag : Bool) :
    ∀ z ∈ support ((simulateQ (handler lenient setup) (shareComp adversary limit pk)).run
        (St.start, flag)),
      z.2.1.record.length ≤ limit + 3929 + 259 :=
  length_shareComp_of (handler lenient setup) lenient setup (fun _ => rfl)
    (length_claims_le lenient setup) adversary limit pk flag

/-- **The filing handler's record is no longer.** -/
theorem length_filing_shareComp (setup : Setup) (adversary : Adversary) (limit : Nat)
    (pk : PublicKey) (flag : Bool) :
    ∀ z ∈ support ((simulateQ (filing setup) (shareComp adversary limit pk)).run
        (St.start, flag)),
      z.2.1.record.length ≤ limit + 3929 + 259 :=
  length_shareComp_of (filing setup) false setup (filing_inl setup)
    (fun forgery p z hz => by
      rw [filing_run, support_map] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      exact length_claims_le false setup forgery (p.1, false) w hw)
    adversary limit pk flag

/-! ## The blind step never reads `SK.prf` -/

theorem pk_prf (publicSeed : Digest) (cells : Cells) (prf prf' : Digest) (pad : Padding) :
    (setupOf publicSeed cells (prf, pad)).pk = (setupOf publicSeed cells (prf', pad)).pk := rfl

theorem route_prf (publicSeed : Digest) (cells : Cells) (prf prf' : Digest) (pad : Padding)
    (state : St) (input : Bytes) :
    route false (setupOf publicSeed cells (prf, pad)) state input =
      route false (setupOf publicSeed cells (prf', pad)) state input := by
  classical
  unfold route
  rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true,
    if_neg (fun h => Bool.false_ne_true h.1), if_neg (fun h => Bool.false_ne_true h.1)]
  rfl

theorem cellSig_prf (publicSeed : Digest) (cells : Cells) (prf prf' : Digest) (pad : Padding)
    (randomizer : Digest) (digest : HashOutput) :
    ShareSigner.cellSig (setupOf publicSeed cells (prf, pad)).warm
        (setupOf publicSeed cells (prf, pad)).sk randomizer digest =
      ShareSigner.cellSig (setupOf publicSeed cells (prf', pad)).warm
        (setupOf publicSeed cells (prf', pad)).sk randomizer digest :=
  ShareSignCongr.cellSig_congr publicSeed prf prf' (cells, pad) (cells, pad)
    (fun _ => Finset.univ) (fun _ _ => rfl) randomizer digest (fun _ => Finset.mem_univ _)

theorem claimsOf_prf (publicSeed : Digest) (cells : Cells) (prf prf' : Digest) (pad : Padding)
    (state : St) (forgery : Forgery) :
    claimsOf (setupOf publicSeed cells (prf, pad)) state forgery =
      claimsOf (setupOf publicSeed cells (prf', pad)) state forgery := rfl

/-- **The blind step is the same at every `SK.prf`.** -/
theorem blindStep_prf (publicSeed : Digest) (cells : Cells) (prf prf' : Digest) (pad : Padding) :
    blindStep (setupOf publicSeed cells (prf, pad)) =
      blindStep (setupOf publicSeed cells (prf', pad)) := by
  classical
  funext queried state
  rcases queried with ((world | request) | ⟨request, drawn⟩) | forgery
  · rcases world with coin | input
    · rfl
    · simp only [blindStep, route_prf publicSeed cells prf prf' pad]
  · cases hframe : request.frame with
    | none => simp only [blindStep, hframe]
    | some framed =>
      simp only [blindStep, hframe, route_prf publicSeed cells prf prf' pad,
        pk_prf publicSeed cells prf prf' pad]
  · cases drawn with
    | none => rfl
    | some pair =>
      obtain ⟨randomizer, digest⟩ := pair
      simp only [blindStep, cellSig_prf publicSeed cells prf prf' pad]
  · simp only [blindStep, claimsOf_prf publicSeed cells prf prf' pad]

/-! ## Expectations, on the support -/

theorem ex_mono_support {β : Type} (mx : ProbComp β) {f g : β → ℝ≥0∞}
    (h : ∀ x ∈ support mx, f x ≤ g x) : BlindCharge.ex mx f ≤ BlindCharge.ex mx g := by
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : x ∈ support mx
  · exact mul_le_mul' le_rfl (h x hx)
  · rw [probOutput_eq_zero_of_not_mem_support hx, zero_mul, zero_mul]

theorem ex_const_le {β : Type} (mx : ProbComp β) (c : ℝ≥0∞) :
    BlindCharge.ex mx (fun _ => c) ≤ c := by
  unfold BlindCharge.ex
  rw [ENNReal.tsum_mul_right]
  exact le_trans (mul_le_mul' tsum_probOutput_le_one le_rfl) (by rw [one_mul])

theorem ex_add {β : Type} (mx : ProbComp β) (f g : β → ℝ≥0∞) :
    BlindCharge.ex mx f + BlindCharge.ex mx g = BlindCharge.ex mx (fun x => f x + g x) := by
  unfold BlindCharge.ex
  rw [← ENNReal.tsum_add]
  exact tsum_congr fun x => (mul_add _ _ _).symm

/-- A draw nothing after it reads leaves an event's chance alone. -/
theorem probEvent_bind_const {β γ : Type} (mx : ProbComp β) (f : β → ProbComp γ)
    (event : γ → Prop) (c : ℝ≥0∞) (h : ∀ x, Pr[event | f x] = c) : Pr[event | mx >>= f] = c := by
  rw [probEvent_bind_eq_tsum]
  simp only [h]
  rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (by simp), one_mul]

/-! ## A located entry is prefixed by the public seed -/

theorem seedPrefixed_of_locate (publicSeed : Digest) (input : Bytes)
    (hlocate : ((GraphStakes.stakes publicSeed).locate input).isSome) :
    Target127.SeedPrefixed publicSeed input := by
  classical
  change (GraphStakes.locate publicSeed input).isSome at hlocate
  unfold GraphStakes.locate at hlocate
  split at hlocate
  · rename_i hsome
    obtain ⟨node, cell, rfl⟩ := hsome
    exact ⟨node.parent.address.toBytes ++ bytesBE n cell,
      by simp [GraphStakes.inputOf, Hashing.tweakableInput, List.append_assoc]⟩
  · simp at hlocate

open scoped Classical in
/-- Each entry is a locating one or one not prefixed by the public seed, not both. -/
theorem countP_located_add_le (publicSeed : Digest) (entries : List (Bytes × List HashOutput)) :
    entries.countP (fun entry => ((GraphStakes.stakes publicSeed).locate entry.1).isSome) +
        entries.countP (fun entry => decide (¬ Target127.SeedPrefixed publicSeed entry.1)) ≤
      entries.length := by
  induction entries with
  | nil => simp
  | cons entry rest ih =>
    simp only [List.countP_cons, List.length_cons]
    by_cases hlocate : ((GraphStakes.stakes publicSeed).locate entry.1).isSome
    · have hprefixed := seedPrefixed_of_locate publicSeed entry.1 hlocate
      have h1 : (if ((GraphStakes.stakes publicSeed).locate entry.1).isSome = true then 1 else 0)
          = 1 := if_pos hlocate
      have h2 : (if decide (¬ Target127.SeedPrefixed publicSeed entry.1) = true then 1 else 0)
          = 0 := if_neg (by simpa using hprefixed)
      rw [h1, h2]
      omega
    · have h1 : (if ((GraphStakes.stakes publicSeed).locate entry.1).isSome = true then 1 else 0)
          = 0 := if_neg hlocate
      have h2 : (if decide (¬ Target127.SeedPrefixed publicSeed entry.1) = true then 1 else 0)
          ≤ 1 := by split_ifs <;> omega
      rw [h1]
      omega

/-! ## The two games at a public seed -/

/-- The blind run at a setup, flag carried. -/
noncomputable def flagRun (comp : PublicKey → OracleComp ShareSpec (Forgery × Bool)) (setup : Setup) :
    ProbComp ((Forgery × Bool) × (St × Bool)) :=
  (simulateQ (handler false setup) (comp setup.pk)).run (St.start, false)

/-- The blind run at a setup, flag dropped. -/
noncomputable def blindRun (comp : PublicKey → OracleComp ShareSpec (Forgery × Bool)) (setup : Setup) :
    ProbComp ((Forgery × Bool) × St) :=
  (simulateQ (blindStep setup) (comp setup.pk)).run St.start

/-- The blind run at a setup in its filing form, flag carried. -/
noncomputable def filingRun (comp : PublicKey → OracleComp ShareSpec (Forgery × Bool))
    (setup : Setup) : ProbComp ((Forgery × Bool) × (St × Bool)) :=
  (simulateQ (filing setup) (comp setup.pk)).run (St.start, false)

theorem map_filingRun (comp : PublicKey → OracleComp ShareSpec (Forgery × Bool)) (setup : Setup) :
    (fun z => (z.1, z.2.1)) <$> filingRun comp setup = blindRun comp setup :=
  map_run_filing setup _ St.start false

theorem blindRun_prf (comp : PublicKey → OracleComp ShareSpec (Forgery × Bool)) (publicSeed prf prf' : Digest)
    (table : Cells × Padding) :
    blindRun comp ⟨prf, publicSeed, table⟩ =
      blindRun comp ⟨prf', publicSeed, table⟩ := by
  show (simulateQ (blindStep (setupOf publicSeed table.1 (prf, table.2)))
      (comp (setupOf publicSeed table.1 (prf, table.2)).pk)).run St.start =
    (simulateQ (blindStep (setupOf publicSeed table.1 (prf', table.2)))
      (comp (setupOf publicSeed table.1 (prf', table.2)).pk)).run St.start
  rw [blindStep_prf publicSeed table.1 prf prf' table.2, pk_prf publicSeed table.1 prf prf' table.2]

theorem length_blindRun (adversary : Adversary) (limit : Nat) (setup : Setup)
    (z : (Forgery × Bool) × St)
    (hz : z ∈ support (blindRun (shareComp adversary limit) setup)) :
    z.2.record.length ≤ limit + 3929 + 259 := by
  rw [← map_filingRun, support_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  exact length_filing_shareComp setup adversary limit setup.pk false w hw

/-- **The blind game at a public seed**: `SK.prf` and the table drawn, the run beside them. -/
noncomputable def flagGame (publicSeed : Digest) (comp : PublicKey → OracleComp ShareSpec (Forgery × Bool)) :
    ProbComp (Setup × ((Forgery × Bool) × (St × Bool))) := do
  let prf ← ($ᵗ Digest : ProbComp Digest)
  let table ← ($ᵗ (Cells × Padding) : ProbComp (Cells × Padding))
  let z ← flagRun comp ⟨prf, publicSeed, table⟩
  pure (⟨prf, publicSeed, table⟩, z)

/-- The same, flag dropped. -/
noncomputable def blindGame (publicSeed : Digest) (comp : PublicKey → OracleComp ShareSpec (Forgery × Bool)) :
    ProbComp (Setup × ((Forgery × Bool) × St)) := do
  let prf ← ($ᵗ Digest : ProbComp Digest)
  let table ← ($ᵗ (Cells × Padding) : ProbComp (Cells × Padding))
  let z ← blindRun comp ⟨prf, publicSeed, table⟩
  pure (⟨prf, publicSeed, table⟩, z)

/-- The same, in the filing form. -/
noncomputable def filingGame (publicSeed : Digest)
    (comp : PublicKey → OracleComp ShareSpec (Forgery × Bool)) :
    ProbComp (Setup × ((Forgery × Bool) × (St × Bool))) := do
  let prf ← ($ᵗ Digest : ProbComp Digest)
  let table ← ($ᵗ (Cells × Padding) : ProbComp (Cells × Padding))
  let z ← filingRun comp ⟨prf, publicSeed, table⟩
  pure (⟨prf, publicSeed, table⟩, z)

theorem map_filingGame (publicSeed : Digest)
    (comp : PublicKey → OracleComp ShareSpec (Forgery × Bool)) :
    (fun w => (w.1, (w.2.1, w.2.2.1))) <$> filingGame publicSeed comp =
      blindGame publicSeed comp := by
  simp only [filingGame, blindGame, map_bind, map_pure, ← map_filingRun, bind_map_left]

/-- **The flag, off a bad walk, has the same law in the blind run and its filing form.** -/
theorem probEvent_flagRun_eq (comp : PublicKey → OracleComp ShareSpec (Forgery × Bool))
    (setup : Setup) :
    Pr[fun z => setup.Good ∧ z.2.2 = true | flagRun comp setup] =
      Pr[fun z => setup.Good ∧ z.2.2 = true | filingRun comp setup] := by
  by_cases hgood : setup.Good
  · simp only [hgood, true_and]
    exact (probEvent_filing_eq _ _ St.start).symm
  · simp [hgood]

/-- **The same in the game.** -/
theorem probEvent_flagGame_eq (publicSeed : Digest)
    (comp : PublicKey → OracleComp ShareSpec (Forgery × Bool)) :
    Pr[fun w => w.1.Good ∧ w.2.2.2 = true | flagGame publicSeed comp] =
      Pr[fun w => w.1.Good ∧ w.2.2.2 = true | filingGame publicSeed comp] := by
  unfold flagGame filingGame
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  refine tsum_congr fun prf => congrArg (_ * ·) ?_
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  refine tsum_congr fun table => congrArg (_ * ·) ?_
  rw [bind_pure_comp, bind_pure_comp, probEvent_map, probEvent_map]
  exact probEvent_flagRun_eq comp _

/-- The blind run at a drawn table, `SK.prf` fixed at a default. -/
noncomputable def tableGame (publicSeed : Digest) (comp : PublicKey → OracleComp ShareSpec (Forgery × Bool)) :
    ProbComp ((Cells × Padding) × ((Forgery × Bool) × St)) := do
  let table ← ($ᵗ (Cells × Padding) : ProbComp (Cells × Padding))
  let z ← blindRun comp ⟨default, publicSeed, table⟩
  pure (table, z)

/-! ## The flag is a union of guesses -/

/-- **Off a bad walk, the flag is a guess the record holds**: a sensitive probe, or a probe not
prefixed by the public seed that is in the `PRF_msg` class at `SK.prf`. -/
theorem flag_le (publicSeed : Digest) (comp : PublicKey → OracleComp ShareSpec (Forgery × Bool)) :
    Pr[fun w => w.1.Good ∧ w.2.2.2 = true | flagGame publicSeed comp] ≤
      Pr[fun w => (∃ entry ∈ w.2.2.record, Sens w.1 entry.2 entry.1) ∨
          (∃ entry ∈ w.2.2.record, ¬ Target127.SeedPrefixed publicSeed entry.1 ∧
            RandomizerGate.PrfClass w.1.prf entry.1) |
        blindGame publicSeed comp] := by
  rw [probEvent_flagGame_eq, ← map_filingGame, probEvent_map]
  refine probEvent_mono fun w hw hevent => ?_
  obtain ⟨hgood, hflag⟩ := hevent
  simp only [filingGame, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hw
  obtain ⟨prf, -, table, -, z, hz, rfl⟩ := hw
  rcases filing_witness _ _ St.start z hz hflag with hbad | ⟨entry, hentry, hguess⟩
  · exact absurd hgood hbad
  · rcases hguess with hsens | hprf
    · exact Or.inl ⟨entry, hentry, hsens⟩
    · refine Or.inr ⟨entry, hentry, fun hprefixed => ?_, hprf⟩
      exact hgood.1 (Target127.eq_of_seedPrefixed (Target127.seedPrefixed_of_prfClass hprf)
        hprefixed)

/-! ## The cell guesses -/

/-- What a frozen run answers: anything. -/
def stall : (queried : ShareSpec.Domain) → ShareSpec.Range queried
  | Sum.inl (Sum.inl (Sum.inl (Sum.inl coin))) => (0 : Fin (coin + 1))
  | Sum.inl (Sum.inl (Sum.inl (Sum.inr _))) => (0 : HashOutput)
  | Sum.inl (Sum.inl (Sum.inr _)) => none
  | Sum.inl (Sum.inr _) => none
  | Sum.inr _ => ()

set_option maxHeartbeats 1000000 in
/-- **The cell guesses cost one unit per locating entry.** -/
theorem sens_le (publicSeed : Digest) (comp : PublicKey → OracleComp ShareSpec (Forgery × Bool)) :
    Pr[fun w => ∃ entry ∈ w.2.2.record, Sens w.1 entry.2 entry.1 |
        blindGame publicSeed comp] ≤
      BlindCharge.ex (tableGame publicSeed comp) (fun tz =>
        ((tz.2.2.record.countP fun entry =>
          ((GraphStakes.stakes publicSeed).locate entry.1).isSome : Nat) : ℝ≥0∞)) /
        ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  have hmarginal : Pr[fun w => ∃ entry ∈ w.2.2.record, Sens w.1 entry.2 entry.1 |
        blindGame publicSeed comp] =
      Pr[fun tz => ∃ entry ∈ tz.2.2.record, Sens ⟨default, publicSeed, tz.1⟩ entry.2 entry.1 |
        tableGame publicSeed comp] := by
    unfold blindGame
    refine probEvent_bind_const _ _ _ _ fun prf => ?_
    unfold tableGame
    simp only [blindRun_prf comp publicSeed prf default]
    rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
    refine tsum_congr fun table => ?_
    congr 1
    rw [bind_pure_comp, bind_pure_comp, probEvent_map, probEvent_map]
    rfl
  have hexperiment : tableGame publicSeed comp =
      (fun w => ((w.2.1, w.2.2), w.1)) <$> BlindCharge.experiment ($ᵗ Padding : ProbComp Padding)
        (fun cells pad => blindRun comp (setupOf publicSeed cells (default, pad))) := by
    unfold tableGame BlindCharge.experiment
    rw [BlockViews.uniformSample_prod_eq_bind]
    simp only [bind_assoc, pure_bind, map_bind, map_pure]
    rfl
  rw [hmarginal, hexperiment, probEvent_map, BlindCharge.ex_map]
  exact BlindCharge.prob_sensitive_le (GraphStakes.stakes publicSeed) St.record St.served
    ($ᵗ Padding : ProbComp Padding)
    (fun cells pad => blindStep (setupOf publicSeed cells (default, pad)))
    (fun cells pad => comp (setupOf publicSeed cells (default, pad)).pk)
    St.start rfl (fun cells pad served node => ¬ available (setupOf publicSeed cells (default, pad))
      served node) stall (fun index => ¬ AlwaysAvailable index)
    (fun cells pad served index hunavailable =>
      not_alwaysAvailable_of_unavailable _ served index hunavailable)
    (fun _ _ _ _ => probFailure_eq_zero)
    (fun cells pad => files_blindStep _)
    (fun index _ cells pad t st hst z hz hunavailable => hunavailable
      (available_mono _ (fun digest hdigest => (served_prefix _ t st z hz).subset hdigest) index
        (not_not.mp hst)))
    (fun index _ cells other pad hagree t st hunavailable =>
      blindStep_congr publicSeed index cells other (default, pad) hagree t st hunavailable)
    (fun index hindex cells other pad hagree served => by
      rw [available_congr publicSeed cells other (default, pad)
        (agree_alwaysAvailable index hindex cells other hagree)])
    (fun index hindex cells other pad hagree => by
      show comp (setupOf publicSeed cells (default, pad)).pk =
        comp (setupOf publicSeed other (default, pad)).pk
      rw [pk_congr publicSeed index hindex cells other (default, pad) hagree])

/-! ## The `SK.prf` guesses -/

open scoped Classical in
/-- **Against a fresh `SK.prf`, an entry not prefixed by the public seed is one guess.** -/
theorem prob_prf_list_le (publicSeed : Digest) (entries : List (Bytes × List HashOutput)) :
    Pr[fun prf : Digest => ∃ entry ∈ entries, ¬ Target127.SeedPrefixed publicSeed entry.1 ∧
        RandomizerGate.PrfClass prf entry.1 | ($ᵗ Digest : ProbComp Digest)] ≤
      ((entries.countP fun entry => decide (¬ Target127.SeedPrefixed publicSeed entry.1) : Nat) :
        ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  refine le_trans (probEvent_mono (q := fun prf : Digest =>
    ∃ entry ∈ (entries.filter fun entry =>
        decide (¬ Target127.SeedPrefixed publicSeed entry.1)).toFinset,
      RandomizerGate.prfGuess entry.1 = prf) ?_) ?_
  · rintro prf - ⟨entry, hentry, hprefixed, hclass⟩
    refine ⟨entry, List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hentry, by simpa using hprefixed⟩),
      ?_⟩
    obtain ⟨seed, message, hinput⟩ := hclass
    rw [hinput, RandomizerGate.prfGuess_randomizerInput]
  refine le_trans (probEvent_exists_finset_le_sum _ _ _) ?_
  refine le_trans (Finset.sum_le_sum fun entry _ =>
    le_of_eq (SecretGuessCharge.prob_single_guess (RandomizerGate.prfGuess entry.1))) ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
  refine ENNReal.div_le_div_right (Nat.cast_le.mpr ?_) _
  rw [List.countP_eq_length_filter]
  exact List.toFinset_card_le _

open scoped Classical in
/-- **The `SK.prf` guesses cost one unit per entry not prefixed by the public seed.** -/
theorem prf_le (publicSeed : Digest) (comp : PublicKey → OracleComp ShareSpec (Forgery × Bool)) :
    Pr[fun w => ∃ entry ∈ w.2.2.record, ¬ Target127.SeedPrefixed publicSeed entry.1 ∧
          RandomizerGate.PrfClass w.1.prf entry.1 |
        blindGame publicSeed comp] ≤
      BlindCharge.ex (tableGame publicSeed comp) (fun tz =>
        ((tz.2.2.record.countP fun entry =>
          decide (¬ Target127.SeedPrefixed publicSeed entry.1) : Nat) : ℝ≥0∞)) /
        ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  have hlaw : 𝒟[blindGame publicSeed comp] =
      𝒟[tableGame publicSeed comp >>= fun tz =>
        ($ᵗ Digest : ProbComp Digest) >>= fun prf =>
          (pure (⟨prf, publicSeed, tz.1⟩, tz.2) : ProbComp (Setup × ((Forgery × Bool) × St)))] := by
    unfold blindGame tableGame
    simp only [blindRun_prf comp publicSeed _ default]
    have hshape : ∀ prf : Digest,
        (do
          let table ← ($ᵗ (Cells × Padding) : ProbComp (Cells × Padding))
          let z ← blindRun comp ⟨default, publicSeed, table⟩
          (pure (⟨prf, publicSeed, table⟩, z) : ProbComp (Setup × ((Forgery × Bool) × St)))) =
        (do
          let table ← ($ᵗ (Cells × Padding) : ProbComp (Cells × Padding))
          let z ← blindRun comp ⟨default, publicSeed, table⟩
          pure (table, z)) >>= fun tz =>
            (pure (⟨prf, publicSeed, tz.1⟩, tz.2) : ProbComp (Setup × ((Forgery × Bool) × St))) := by
      intro prf
      simp only [bind_assoc, pure_bind]
    simp only [hshape]
    exact OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
  rw [probEvent_congr' (fun _ _ => Iff.rfl) hlaw, BlindCharge.probEvent_eq_ex_bind,
    ← BlindCharge.ex_div_const]
  refine BlindCharge.ex_mono _ fun tz => ?_
  rw [bind_pure_comp, probEvent_map]
  exact prob_prf_list_le publicSeed tz.2.2.record

/-! ## The bound -/

open scoped Classical in
/-- **The entries a charge pays for**: those locating a node, and those not prefixed by the
public seed. -/
noncomputable def charged (publicSeed : Digest) (record : List (Bytes × List HashOutput)) : Nat :=
  record.countP (fun entry => ((GraphStakes.stakes publicSeed).locate entry.1).isSome) +
    record.countP (fun entry => decide (¬ Target127.SeedPrefixed publicSeed entry.1))

theorem charged_le_length (publicSeed : Digest) (record : List (Bytes × List HashOutput)) :
    charged publicSeed record ≤ record.length := by
  classical
  unfold charged
  convert countP_located_add_le publicSeed record

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
/-- **The blind game's flag, off a bad walk, is at most the charged entries over `2 ^ 128`**,
for any game whose blind runs keep the charged entries within `bound`. -/
theorem blind_bound_of (publicSeed : Digest)
    (comp : PublicKey → OracleComp ShareSpec (Forgery × Bool)) (bound : Nat)
    (hbound : ∀ setup : Setup, ∀ z ∈ support (blindRun comp setup),
      charged publicSeed z.2.record ≤ bound) :
    Pr[fun w => w.1.Good ∧ w.2.2.2 = true | flagGame publicSeed comp] ≤
      (bound : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  refine le_trans (flag_le publicSeed comp) ?_
  refine le_trans (probEvent_or_le _ _ _) ?_
  refine le_trans (add_le_add (sens_le publicSeed comp)
    (prf_le publicSeed comp)) ?_
  rw [ENNReal.div_add_div_same, ex_add]
  refine ENNReal.div_le_div_right ?_ _
  refine le_trans (ex_mono_support _ fun tz htz => ?_) (ex_const_le _ _)
  rw [← Nat.cast_add]
  refine Nat.cast_le.mpr ?_
  simp only [tableGame, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at htz
  obtain ⟨table, -, z, hz, rfl⟩ := htz
  have h := hbound _ z hz
  unfold charged at h
  convert h

/-- **The blind game's flag, off a bad walk, is at most `(limit + 3929 + 259) / 2 ^ 128`.** -/
theorem blind_bound (publicSeed : Digest) (adversary : Adversary) (limit : Nat) :
    Pr[fun w => w.1.Good ∧ w.2.2.2 = true | flagGame publicSeed (shareComp adversary limit)] ≤
      ((limit + 3929 + 259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) :=
  blind_bound_of publicSeed (shareComp adversary limit) _ fun setup z hz =>
    (charged_le_length publicSeed _).trans (length_blindRun adversary limit setup z hz)

end SlhDsaSecurity.ShareBound
