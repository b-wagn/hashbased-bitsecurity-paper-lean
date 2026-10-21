import SlhDsaSecurity.Proof.SeedDeferral
import VCVio.StateSeparating.IdenticalUntilBad

/-!
# The input-side coupling

The answer side of the budget charges events about a query's *answer*. The input side charges
the one event that is about a query's *input*: that the adversary names a byte string which is
the honest input at some coordinate of the hypertree, i.e. that it has guessed `SK.seed`.

`SecretGuessCharge.prob_secret_guessed_le` already bounds that at `q / 2 ^ 128`, but it samples
the secret *after* the run. The experiment samples it at key generation, before the adversary
starts. This file carries out the hop that bridges the two, as an identical-until-bad step over
`QueryImpl.Stateful.advantage_le_expectedQuerySlack_plus_probEvent_bad`.

## Why the seed cannot sit in the handler state

The per-step hypothesis of that theorem is quantified over *every* state `s`:

```
∀ t s, tvDist ((h₀ t).run (s, false)) ((h₁ t).run (s, false)) ≤ querySlack s
```

If the state held the seed, this would be false pointwise: at the one input that is seed-derived
for that `s` the two handlers return different answers, so their distance is `1`, not `2 ^ -128`.
The hypothesis can only hold if the seed is *not* in the state — which is to say, if the handler
draws it lazily, inside the step, at the moment it has to decide whether the input it was handed
is seed-derived. That moment is exactly when the bad flag fires, so the deferral costs nothing:
after the flag is set the two worlds are allowed to diverge arbitrarily.

This is what `real` below does. Its state carries the adversary's own cache together with the
*coordinate-keyed* honest table — the honest answers indexed by hypertree coordinate rather than
by byte input. That the honest table can be keyed this way, with the seed appearing only in the
cache keys the adversary never sees, is `SeedDeferral.honest_result_indep_of_seed`.

## What is proved here

* `tvDist_step_le` — the per-step total-variation bound, at rate `2 ^ -128`, from
  `SeedDeferral.prob_honest_key_le`;
* `step_eq_of_uncharged`, `real_bad_monotone` — the other two hypotheses of the hop;
* `advantage_le` — the hop itself, giving `advantage ≤ q / 2 ^ 128 + Pr[bad]`;
* `probEvent_bad_le` — the bad-flag mass is itself at most `q / 2 ^ 128`, so
* `advantage_le_two_mul` — the separation, `advantage ≤ 2 * q / 2 ^ 128`.

## What is *not* proved here

That `real` is the real experiment. `real` resamples the seed at every step; the real game draws
it once at key generation. The two agree because the honest transcript does not depend on the
seed (`SeedDeferral.honest_result_indep_of_seed`, `honest_result_defer_seed`), but turning those
two lemmas into an equality of the two *handlers* is a separate step and is not carried out in
this file. What is established here is the quantitative half: against a handler that answers
every query freshly, the lazily-seeded handler is `2q / 2 ^ 128`-indistinguishable.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.InputCoupling

variable {Index : Type}

/-! ## The two handlers -/

/-- The handler state: the adversary's own cache, together with the honest answers keyed by
hypertree *coordinate*. No seed appears, by design — see the module docstring. -/
abbrev State (Index : Type) : Type := QueryCache HashSpec × (Index → HashOutput)

/-- Whether `candidate` is the honest input at the coordinate its address field names.

The address field is carried in the clear by the FIPS 205 byte format, so `locate` reads off the
only coordinate `candidate` could be the honest input of, and one equality test settles it. -/
def SeedDerived (inputOf : Digest → Index → Bytes) (locate : Bytes → Option Index)
    (secret : Digest) (candidate : Bytes) : Prop :=
  ∃ node : Index, locate candidate = some node ∧ inputOf secret node = candidate

instance (inputOf : Digest → Index → Bytes) (locate : Bytes → Option Index)
    (secret : Digest) (candidate : Bytes) :
    Decidable (SeedDerived inputOf locate secret candidate) := by
  unfold SeedDerived
  cases locate candidate with
  | none => exact isFalse (by rintro ⟨node, hnode, -⟩; exact absurd hnode (by simp))
  | some node =>
    by_cases heq : inputOf secret node = candidate
    · exact isTrue ⟨node, rfl, heq⟩
    · refine isFalse ?_
      rintro ⟨other, hother, hval⟩
      exact heq (Option.some.inj hother ▸ hval)

/-- The honest answer at `candidate`, read out of the coordinate-keyed table. -/
def honestAnswer (locate : Bytes → Option Index) (honest : Index → HashOutput)
    (candidate : Bytes) : HashOutput :=
  match locate candidate with
  | none => default
  | some node => honest node

/-- **The blind handler.** Every adversary query is answered freshly, by a lazy random oracle on
the adversary's own cache. Nothing about the key is consulted, and the bad flag never moves. -/
def blind : QueryImpl.Stateful unifSpec HashSpec (State Index × Bool) :=
  fun candidate => StateT.mk fun p => do
    let z ← (randomOracle candidate).run p.1.1
    return (z.1, ((z.2, p.1.2), p.2))

/-- **The real handler.** It draws the secret seed *at the step*, uses it only to decide whether
the input it was handed is the honest input at some coordinate, and if so answers out of the
honest table and raises the bad flag. On every other input it coincides with `blind`, seed and
all. The seed is never written to the state: it exists only for the duration of one step. -/
def real (inputOf : Digest → Index → Bytes) (locate : Bytes → Option Index) :
    QueryImpl.Stateful unifSpec HashSpec (State Index × Bool) :=
  fun candidate => StateT.mk fun p => do
    let secret ← ($ᵗ Digest : ProbComp Digest)
    if SeedDerived inputOf locate secret candidate then
      return (honestAnswer locate p.1.2 candidate, (p.1, true))
    else
      let z ← (randomOracle candidate).run p.1.1
      return (z.1, ((z.2, p.1.2), p.2))

/-! ## The three hypotheses of the identical-until-bad hop -/

/-- A `SeedDerived` input is in particular an honest input at *some* coordinate, which is the
event `SeedDeferral.prob_honest_key_le` charges. -/
theorem probEvent_seedDerived_le (inputOf : Digest → Index → Bytes)
    (locate : Bytes → Option Index)
    (hlocate : ∀ (secret : Digest) (node : Index), locate (inputOf secret node) = some node)
    (hinj : ∀ node : Index, Function.Injective (fun secret : Digest => inputOf secret node))
    (candidate : Bytes) :
    Pr[fun secret : Digest => SeedDerived inputOf locate secret candidate |
      ($ᵗ Digest : ProbComp Digest)] ≤ 1 / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  refine le_trans (probEvent_mono (α := Digest)
    (q := fun secret : Digest => ∃ node : Index, inputOf secret node = candidate) ?_) ?_
  · rintro secret - ⟨node, -, hnode⟩
    exact ⟨node, hnode⟩
  · exact SeedDeferral.prob_honest_key_le inputOf locate hlocate hinj candidate

/-- Both handlers answer freshly once the seed is drawn and found not to match. -/
theorem real_step_eq (inputOf : Digest → Index → Bytes) (locate : Bytes → Option Index)
    (candidate : Bytes) (p : State Index × Bool) :
    (real inputOf locate candidate).run p =
      (($ᵗ Digest : ProbComp Digest) >>= fun secret =>
        if SeedDerived inputOf locate secret candidate then
          (pure (honestAnswer locate p.1.2 candidate, (p.1, true)) :
            ProbComp (HashOutput × (State Index × Bool)))
        else (blind candidate).run p) := rfl

/-- The blind step may be preceded by a draw of the seed it ignores. -/
theorem evalDist_blind_step (candidate : Bytes) (p : State Index × Bool) :
    𝒟[(blind candidate).run p] =
      𝒟[(($ᵗ Digest : ProbComp Digest) >>= fun _ => (blind candidate).run p)] :=
  (OracleComp.DeferredSampling.evalDist_bind_const_neverFails _ (by simp) _).symm

/-- **The per-step total-variation bound.** At a state with the bad flag down, the real and blind
handlers are `2 ^ -128`-close, at *every* state — which is possible only because the state holds
no seed. -/
theorem tvDist_step_le (inputOf : Digest → Index → Bytes) (locate : Bytes → Option Index)
    (hlocate : ∀ (secret : Digest) (node : Index), locate (inputOf secret node) = some node)
    (hinj : ∀ node : Index, Function.Injective (fun secret : Digest => inputOf secret node))
    (candidate : Bytes) (s : State Index) :
    ENNReal.ofReal
        (tvDist ((real inputOf locate candidate).run (s, false))
          ((blind candidate).run (s, false))) ≤ 1 / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  have hrw : tvDist ((real inputOf locate candidate).run (s, false))
        ((blind candidate).run (s, false)) =
      tvDist (($ᵗ Digest : ProbComp Digest) >>= fun secret =>
          if SeedDerived inputOf locate secret candidate then
            (pure (honestAnswer locate s.2 candidate, ((s, true) : State Index × Bool)) :
              ProbComp (HashOutput × (State Index × Bool)))
          else (blind candidate).run (s, false))
        (($ᵗ Digest : ProbComp Digest) >>= fun _ =>
          (blind candidate).run ((s, false) : State Index × Bool)) := by
    simp only [tvDist, real_step_eq, ← evalDist_blind_step]
  rw [hrw]
  refine le_trans (ofReal_tvDist_bind_left_event_le _ _ _
    (fun secret => SeedDerived inputOf locate secret candidate) ?_) ?_
  · intro secret hsecret
    simp [hsecret]
  · exact probEvent_seedDerived_le inputOf locate hlocate hinj candidate

/-- **Agreement on uncharged queries.** Every query is charged, so there is nothing to check. -/
theorem step_eq_of_uncharged (inputOf : Digest → Index → Bytes) (locate : Bytes → Option Index)
    (candidate : Bytes) (huncharged : ¬ (True : Prop)) (p : State Index × Bool) :
    (real inputOf locate candidate).run p = (blind candidate).run p :=
  absurd trivial huncharged

/-- **Bad-flag monotonicity.** Neither branch of `real` ever lowers the flag. -/
theorem real_bad_monotone (inputOf : Digest → Index → Bytes) (locate : Bytes → Option Index)
    (candidate : Bytes) (p : State Index × Bool) (hp : p.2 = true) :
    ∀ z ∈ support ((real inputOf locate candidate).run p), z.2.2 = true := by
  classical
  rintro z hz
  rw [real_step_eq] at hz
  simp only [support_bind, Set.mem_iUnion] at hz
  obtain ⟨secret, -, hz⟩ := hz
  by_cases hsd : SeedDerived inputOf locate secret candidate
  · rw [if_pos hsd] at hz
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    rfl
  · rw [if_neg hsd] at hz
    simp only [blind, StateT.run, StateT.mk, support_bind, support_pure, Set.mem_iUnion,
      Set.mem_singleton_iff] at hz
    obtain ⟨w, -, hz⟩ := hz
    subst hz
    exact hp


/-! ## The hop

With the three hypotheses in hand the identical-until-bad theorem applies verbatim. Every query
is charged, so the budget is the plain query bound and the agreement hypothesis is vacuous. -/

/-- **The input-side coupling.** A distinguisher making at most `queryBudget` queries separates
the lazily-seeded handler from the blind one by at most `queryBudget / 2 ^ 128`, plus the mass of
the event that it actually named a seed-derived input. -/
theorem advantage_le (inputOf : Digest → Index → Bytes) (locate : Bytes → Option Index)
    (hlocate : ∀ (secret : Digest) (node : Index), locate (inputOf secret node) = some node)
    (hinj : ∀ node : Index, Function.Injective (fun secret : Digest => inputOf secret node))
    (s_init : State Index) (A : OracleComp HashSpec Bool) {queryBudget : ℕ}
    (h_bound : OracleComp.IsQueryBoundP A (fun _ : Bytes => True) queryBudget) :
    ENNReal.ofReal
        ((real inputOf locate).advantage (s_init, false) blind (s_init, false) A)
      ≤ queryBudget / ((2 ^ 128 : Nat) : ℝ≥0∞)
        + Pr[fun z : Bool × State Index × Bool => z.2.2 = true |
            (simulateQ (real inputOf locate) A).run (s_init, false)] := by
  refine le_trans (QueryImpl.Stateful.advantage_le_queryBound_mul_slack_plus_probEvent_bad
    (real inputOf locate) blind s_init (fun _ : Bytes => True) (1 / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (fun candidate _ s => tvDist_step_le inputOf locate hlocate hinj candidate s)
    (fun candidate huncharged p => step_eq_of_uncharged inputOf locate candidate huncharged p)
    (fun candidate p hp => real_bad_monotone inputOf locate candidate p hp)
    A h_bound) ?_
  gcongr
  exact le_of_eq (by rw [mul_one_div])

end SlhDsaSecurity.InputCoupling
