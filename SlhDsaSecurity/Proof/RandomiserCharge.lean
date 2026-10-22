import SlhDsaSecurity.Proof.Target
import SlhDsaSecurity.Proof.RandomizerGate
import SlhDsaSecurity.Proof.WarmedCharges

/-!
# Where a `PRF_msg` entry can have come from

`ReplayGate.RandomiserBad` is the cache holding a `PRF_msg` entry at the real seed for a framing
no signing request produced. Charging it means finding the query that made it, and the first
step is to rule out the parts of the run that cannot have.

The warm walk is one of them, and that is what this file proves: the walk programs the canonical
graph and nothing else, a canonical input opens with `PK.seed` and a `PRF_msg` input with
`SK.prf`, and the two seeds differ on a good walk. So a `PRF_msg` entry in the final cache was
made during the tail.

The rest of the provenance is not here, and it has one case that is easy to miss. Key generation
makes no `PRF_msg` query, and the signer's own `PRF_msg` query for a request it served is at
that request's framing, which is not this message. But the *digest* queries are a different
matter: a message input **is** a `PRF_msg` input, at its own randomiser read as the seed
(`RandomizerGate.messageInput_eq_randomizerInput`), so a digest query matches this event's input
exactly when the randomiser it was made under is `SK.prf` itself. For the signer that is one
coincidence per request, and since every request costs at least one counted hash it is paid at
one unit of `2 ^ -128` per request out of the same budget; for the verifier it is the forgery's
own randomiser hitting the seed, which is one more guess. Neither is a hole, but a provenance
argument that forgets the overlap will look like it closes and will not.

What it then takes to charge the event is a deferral, and it is worth saying why nothing shorter
will do. The adversary's queries are not independent of `SK.prf` — the randomisers it sees are
truncations of `PRF_msg` answers at that seed — so the seed cannot simply be drawn afterwards.
What is true is that those answers are a random oracle's at inputs the adversary has not queried,
so they are uniform and independent of the seed *unless* it queries one, which is the event being
charged. That is the hybrid `SeedDeferral` describes and does not yet carry along an execution.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.RandomiserCharge

open Security CanonicalGraph WarmedGame

/-- **The warm cache holds no `PRF_msg` entry at the walk's own seed.** -/
theorem walk_cache_prf_fresh
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk) (hgood : Target.GoodWalk walk)
    (seed : Digest) (message : Bytes) :
    walk.2 (Hashing.randomizerInput walk.1.1.2.1 seed message) = none := by
  by_contra hpresent
  obtain ⟨parent, hcanonical⟩ := WarmedCharges.walk_cache_canonical hwalk _ hpresent
  exact RandomizerGate.canonicalInput_ne_randomizerInput walk.1.1.2.2 walk.1.1.2.1 seed
    walk.1.2 parent message hgood.1 hcanonical.symm

end SlhDsaSecurity.RandomiserCharge
