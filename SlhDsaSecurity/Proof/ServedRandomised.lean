import SlhDsaSecurity.Proof.ServingCarrier
import SlhDsaSecurity.Proof.CacheAvailability

/-!
# The hinge between what is recorded and what fires

Three predicates do three jobs at the carrier and no two of them can be the same.

* **What files** is `HandlerCarrier.FilesLeft`, the flag the signing oracle holds up while it
  serves. It has to be unforgeable, and it is down at every step boundary.
* **What fires** is `CacheAvailability.SignerRandomised`, read at the cache. It has to change
  only where a fresh answer is drawn, because that is where the rate is spent and a
  deterministic step cannot be paid for out of `potential * rate`.
* **What is recorded** is `HandlerCarrier.Served`. It has to be faithful to the signing log,
  because that is what the coverage event reads.

The arrangement only works if the charge on the second bounds the defect stated at the third,
and that is this file: **a served input is signer-randomised at the cache that served it.**

**The proof is not the one it looks like.** The obvious route is through the blindness — filed
means the flag was up, the flag is up only inside a signing sub-run, so the query was the
signer's and used the real randomiser. That argument is correct and it is already made, once, in
proving `ServingCarrier.AgreesWithLog` of a run; redoing it here would be a second framework
saying the same thing. So this takes the agreement as given and does the remaining step, which
is small: the log names a request, its randomiser answer is in the cache, and `replayRandomizer`
is then that answer's truncation rather than the `default` a miss would fabricate.

That `replay` answers a miss with `default` is the same fact that made the provenance hypothesis
false, which is why the second hypothesis below is not optional: without it `logServed` says
something about `truncate default` and nothing about the signer.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.ServedRandomised

open Security ServingCarrier CacheAvailability

/-- **A served input is signer-randomised at the cache that served it.**

The two hypotheses are facts about a *run*, proved where the run is in hand: the carrier served
exactly what the log names, and every logged request's own `PRF_msg` answer is in the cache.
Neither is re-proved here. -/
theorem signerRandomised_of_served (sk : SecretKey) (signed : SigningLog) (state : Carrier)
    (hagree : AgreesWithLog sk signed state)
    (hcached : ∀ entry ∈ signed, ∀ framed : Bytes, entry.1.frame = some framed →
      state.cache (Hashing.randomizerInput sk.prf sk.publicKey.seed framed) ≠ none)
    (input : Bytes) (hserved : Served state input) :
    SignerRandomised sk.prf sk.publicKey state.cache input := by
  classical
  obtain ⟨entry, hentry, framed, hframe, hinput⟩ := (hagree input).mp hserved
  obtain ⟨answer, hanswer⟩ :=
    Option.ne_none_iff_exists'.mp (hcached entry hentry framed hframe)
  refine ⟨framed, answer, hanswer, ?_⟩
  rw [hinput, HonestProbes.replayRandomizer, CacheReplay.replay, hanswer, Option.getD_some]

/-- **So the defect stated at the served set is bounded by the defect stated at the cache.** The
charge pays for the second; this is what lets it answer for the first. -/
theorem signerRandomised_of_served_mem (sk : SecretKey) (signed : SigningLog) (state : Carrier)
    (hagree : AgreesWithLog sk signed state)
    (hcached : ∀ entry ∈ signed, ∀ framed : Bytes, entry.1.frame = some framed →
      state.cache (Hashing.randomizerInput sk.prf sk.publicKey.seed framed) ≠ none)
    (record : List (Bytes × HashOutput))
    (hlate : ∃ pair ∈ record, Served state pair.1) :
    ∃ pair ∈ record, SignerRandomised sk.prf sk.publicKey state.cache pair.1 := by
  obtain ⟨pair, hpair, hserved⟩ := hlate
  exact ⟨pair, hpair, signerRandomised_of_served sk signed state hagree hcached pair.1 hserved⟩

end SlhDsaSecurity.ServedRandomised
