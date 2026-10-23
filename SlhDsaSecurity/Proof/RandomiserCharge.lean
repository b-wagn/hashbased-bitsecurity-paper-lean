import SlhDsaSecurity.Proof.Target
import SlhDsaSecurity.Proof.RandomizerGate
import SlhDsaSecurity.Proof.WarmedCharges
import SlhDsaSecurity.Proof.StrippedGame
import SlhDsaSecurity.Proof.HonestProbes

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

/-! ## The honest phase, stripped, asks nothing new

Stripping removes the queries the warm table can answer and leaves the rest untouched, so the
stripped computation's probes are among the original's. That is what lets `HonestProbes`'
characterisations be read off the game's own honest phase rather than off the scheme in
isolation. -/

/-! ## What the honest phase's `PRF_msg` queries are

With the stripping out of the way, `HonestProbes` settles both honest parties. Key generation
consults canonical inputs only, and a canonical input opens with `PK.seed`. The signer consults
canonical inputs and the two its own framing names — its randomiser's, which is at *that
request's* message, and its digest's, which is a `PRF_msg` input only at its own randomiser. -/

/-! ## The class, as a deferral consumes it

`TrackedQueries.prob_meets_real_le` charges a run one unit of `2 ^ -128` per query for meeting an
input that carries a secret, and it asks for the class in a particular shape: inputs indexed by
a node, with the index readable off the bytes and the input injective in the secret. For the
`PRF_msg` class the node is the pair the format carries beside the seed, and both conditions are
the format's own injectivity. -/

end SlhDsaSecurity.RandomiserCharge
