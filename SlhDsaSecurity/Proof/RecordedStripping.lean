import SlhDsaSecurity.Proof.RecordedTail

/-!
# Stripping the honest phase, with the record kept

`StrippedGame.evalDist_run_strippedAfterSeeds` says that answering key generation and the signer
from the walk's table changes nothing about the law of the run. The input half needs that fact
one presentation along, at the game that **records** the adversary's and the verifier's own
inputs, because the containment the half's weight is paid from is a statement about that record
and the honest phase has to be stripped for it to hold: unstripped, the signer's canonical
probes reach the handler, aim at cells, and are recorded by nobody.

Nothing here is new as an argument. The counted run's congruence is generic in the writer the
phase carries, so it is restated over an arbitrary monoid — `writerRun` and
`evalDist_writerRun_congr` — and the recorded game's stripping is then the same three steps as
the counted game's: key generation agrees because its probes are the table's, the two signing
oracles agree because the stripped signer's run is the signer's, and the phase's law follows by
the congruence.

**It is an equality, not a bound.** Every step of the input half's transport is, and a bound
appearing in one of them would mean a step was not the equality it is taken for.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.RecordedStripping

open Security RecordedQueries StrippedGame

/-! ## The writer's run, over an arbitrary monoid -/

/-- The run of a phase computation carrying a writer, from a log and a cache. -/
noncomputable def writerRun {ω : Type} [Monoid ω] {α : Type}
    (x : WriterT ω (StateT SigningLog (OracleComp OracleWorld)) α) (log : SigningLog)
    (current : QueryCache HashSpec) :
    ProbComp (((α × ω) × SigningLog) × QueryCache HashSpec) :=
  (simulateQ KeygenUniform.rom ((WriterT.run x).run log)).run current

theorem writerRun_bind {ω : Type} [Monoid ω] {α β : Type}
    (x : WriterT ω (StateT SigningLog (OracleComp OracleWorld)) α)
    (next : α → WriterT ω (StateT SigningLog (OracleComp OracleWorld)) β)
    (log : SigningLog) (current : QueryCache HashSpec) :
    writerRun (x >>= next) log current =
      writerRun x log current >>= fun outer =>
        (fun inner => (((inner.1.1.1, outer.1.1.2 * inner.1.1.2), inner.1.2), inner.2)) <$>
          writerRun (next outer.1.1.1) outer.1.2 outer.2 := by
  simp only [writerRun, WriterT.run_bind, StateT.run_bind, StateT.run_map, simulateQ_bind,
    simulateQ_map, StateT.run_map]

/-- **A handler may be replaced by one with the same law**, at every cache carrying the warm
table. The counted case is `StrippedGame.evalDist_countedRun_congr`; nothing in the argument
reads the writer, so it is stated here over any. -/
theorem evalDist_writerRun_congr {ω : Type} [Monoid ω] (warm : QueryCache HashSpec)
    (impl impl' : QueryImpl (OracleWorld + SigningSpec)
      (WriterT ω (StateT SigningLog (OracleComp OracleWorld))))
    (hagree : ∀ (t : (OracleWorld + SigningSpec).Domain) (log : SigningLog)
      (current : QueryCache HashSpec), Extends warm current →
      𝒟[writerRun (impl t) log current] = 𝒟[writerRun (impl' t) log current])
    {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (log : SigningLog) (current : QueryCache HashSpec), Extends warm current →
      𝒟[writerRun (simulateQ impl computation) log current] =
        𝒟[writerRun (simulateQ impl' computation) log current] := by
  induction computation using OracleComp.inductionOn with
  | pure value => intro _ _ _; rfl
  | query_bind t next ih =>
    intro log current hsub
    rw [simulateQ_bind, simulateQ_bind, simulateQ_spec_query, simulateQ_spec_query,
      writerRun_bind, writerRun_bind]
    have hmid : 𝒟[writerRun (impl t) log current >>= fun outer =>
          (fun inner => (((inner.1.1.1, outer.1.1.2 * inner.1.1.2), inner.1.2), inner.2)) <$>
            writerRun (simulateQ impl (next outer.1.1.1)) outer.1.2 outer.2] =
        𝒟[writerRun (impl t) log current >>= fun outer =>
          (fun inner => (((inner.1.1.1, outer.1.1.2 * inner.1.1.2), inner.1.2), inner.2)) <$>
            writerRun (simulateQ impl' (next outer.1.1.1)) outer.1.2 outer.2] :=
      evalDist_bind_congr (fun outer houter => by
        rw [evalDist_map, evalDist_map, ih outer.1.1.1 outer.1.2 outer.2
          (extends_of_mem_support ((WriterT.run (impl t)).run log) warm current hsub outer
            houter)])
    rw [hmid, evalDist_bind, evalDist_bind, hagree t log current hsub]

/-! ## The recorded game, stripped -/

/-- **The two recording signing oracles answer alike** at every cache carrying the warm table. -/
theorem evalDist_writerRun_signingOracle (warm : QueryCache HashSpec) (sk : SecretKey)
    (t : (OracleWorld + SigningSpec).Domain) (log : SigningLog)
    (current : QueryCache HashSpec) (hsub : Extends warm current) :
    𝒟[writerRun ((recordedAdversaryImpl + recordedSigningOracle (Scheme.sign sk)) t) log
        current] =
      𝒟[writerRun ((recordedAdversaryImpl +
        recordedSigningOracle (StrippedGame.strippedSign warm sk)) t) log current] := by
  rcases t with world | request
  · rfl
  · refine congrArg _ ?_
    show (simulateQ KeygenUniform.rom
        (((recordedSigningOracle (Scheme.sign sk) request).run).run log)).run current =
      (simulateQ KeygenUniform.rom
        (((recordedSigningOracle (StrippedGame.strippedSign warm sk) request).run).run
          log)).run current
    rw [run_recordedSigningOracle, run_recordedSigningOracle, simulateQ_bind, simulateQ_bind,
      StateT.run_bind, StateT.run_bind,
      run_strippedSign warm sk request current hsub]

set_option maxHeartbeats 1000000 in
/-- **Stripping the honest phase changes nothing about the law of the recorded run.** -/
theorem evalDist_run_recordedAfterSeeds (adversary : Adversary)
    (sds : Digest × Digest × Digest) (warm current : QueryCache HashSpec)
    (hsub : Extends warm current) :
    𝒟[(simulateQ KeygenUniform.rom
        (RecordedQueries.recordedAfterSeeds adversary sds warm)).run current] =
      𝒟[(simulateQ KeygenUniform.rom
        (RecordedTail.recordedAfterSeeds adversary sds)).run current] := by
  unfold RecordedQueries.recordedAfterSeeds RecordedTail.recordedAfterSeeds
  rw [simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind,
    run_strippedKeygen warm sds current hsub]
  refine evalDist_bind_congr ?_
  rintro ⟨⟨sk, pk⟩, cache⟩ hstep
  have hcache : Extends warm cache :=
    extends_of_mem_support _ warm current hsub ((sk, pk), cache) hstep
  rw [simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind, evalDist_bind,
    evalDist_bind]
  refine congrArg (fun head => head >>= _) ?_
  exact evalDist_writerRun_congr warm _ _
    (fun t log inner hinner =>
      (evalDist_writerRun_signingOracle warm sk t log inner hinner).symm)
    (adversary.main pk) [] cache hcache

end SlhDsaSecurity.RecordedStripping
