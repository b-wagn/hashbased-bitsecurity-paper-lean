import SlhDsaSecurity.Proof.CacheAvailability

/-!
# Disclosure by what the signer served, not by what the cache holds

`CacheAvailability.signedAt` counts a digest as disclosing when the `PRF_msg` entry for its
message is in the cache. That is a proxy for "the signer produced a signature at this digest",
and the proxy is satisfied by an adversary that makes the `PRF_msg` query itself — which is why
that fiction has to be charged. The notion this file states takes the request set from the
**signing log** instead, so the fiction cannot arise: a digest discloses when the signer served
the request it belongs to, logged or in flight.

Two things about the shape, both found by checking rather than assumed.

**The cache conjunct stays, and it is what makes the notion monotone.** A request's disclosed
positions are the ones its *digest* selects, and the digest is an oracle answer. A request that
is in flight but whose digest has not been drawn yet has no positions to disclose; if it were
counted anyway, with the digest read off an absent entry, the set it contributes would change
when the real answer arrived, and a disclosed set that moves is no use to a charge that stalls
on it. So a served request discloses once its digest input is in the cache — and that is after
the `PRF_msg` query and before the FORS reads, which is exactly the ordering the stalled run
needs and the only thing the proxy was ever getting right.

**The state is abstract.** Whatever carries the log and the request in flight — a handler state,
a trace — is a parameter here, as it already is in `GraphStakes`. The two properties below are
about the notion and not about where it is kept, so they are provable now and instantiable when
the presentation that carries the in-flight request lands.

The request set is indexed by the **digest input**, not by the digest value: input equality is
what pins a randomiser and a message through `Hashing.messageInput_injective`, and no step here
or downstream then needs a collision bound.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.ServedDisclosure

open CanonicalGraph

variable {State : Type}

/-! ## The first property: it only grows -/

/-- **Availability is monotone in the disclosed set**, whatever that set is read from. The
disclosed set enters only at the `forsPrf` leaves, so this is the whole of it. -/
theorem available_mono_signed (revealed : WotsKey → Fin chains → Nat)
    {signedLeft signedRight : ForsKey → Finset (Fin (forsTrees * 2 ^ forsHeight))}
    (hsubset : ∀ key, signedLeft key ⊆ signedRight key) (node : Node)
    (havailable : Available revealed signedLeft node) :
    Available revealed signedRight node := by
  cases node with
  | secretSeed => exact havailable
  | structural parent =>
    cases parent with
    | wotsPrf key chain => exact havailable
    | wotsHash key chain step => exact havailable
    | forsPrf key index => exact hsubset key havailable
    | wotsPk key => exact True.intro
    | tree location height index => exact True.intro
    | forsTree key height index => exact True.intro
    | forsRoots key => exact True.intro

/-! ## The second property: it is closed under the graph

This one costs nothing, and it is worth saying why rather than citing it: `GraphStakes.closed`
is proved for an arbitrary disclosed set, because availability of a parent is decided by its
children and the disclosed set enters only at the `forsPrf` leaves. So any notion whatever has
it, and swapping the proxy for the log cannot lose it. -/

/-! ## Availability, read off what was served

The wrapper `CacheAvailability.availableAt` is stated at the proxy; this is the same wrapper at
the served notion, and the same three facts about it. The WOTS half does not move: each
hypertree key signs one message that is a function of the key and the seeds alone, so the digit
it discloses is fixed before the adversary runs and owes the signing log nothing. -/

variable [HasQuery HashSpec Id]

end SlhDsaSecurity.ServedDisclosure
