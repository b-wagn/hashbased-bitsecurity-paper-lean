import SlhDsaSecurity.Proof.Hashing
import SlhDsaSecurity.Proof.GraphFreshSampling
import SlhDsaSecurity.Statement.Security

/-!
# Distinct signing requests query distinct message-digest inputs

This is the first step of the disclosure load cap. The cap depends only on the distribution
of the FORS instances of the signed digests, and a digest is a uniform oracle answer
whichever party queries its input first — a prequery by the adversary does not bias it. So
no freshness argument is needed; all that is required is that distinct signed requests use
*distinct* `H_msg` byte inputs, because distinct inputs in the shared random oracle have
independent uniform answers.

That is what `messageInput_ne_of_request_ne` says, and it holds regardless of the
randomizers: `Hashing.messageInput` is injective in all three of its arguments
(`Hashing.messageInput_injective`), and distinct requests with valid frames have distinct
framed messages (`Message.frame_injective`).

Conversely a repeated request has the *same* digest input, hence the same digest and the same
fourteen disclosed FORS leaves, so it does not enlarge the disclosure sets even though the
all-queries-counted experiment charges it. That direction needs no lemma: the input is a
function of the request.
-/

namespace SlhDsaSecurity.DigestInputDistinct

/-- Distinct signing requests, framed, give distinct `H_msg` inputs — whatever their
randomizers. -/
theorem messageInput_ne_of_request_ne (pk pk' : PublicKey) (left right : Message)
    (framedLeft framedRight : Bytes) (randomizerLeft randomizerRight : Digest)
    (hleft : left.frame = some framedLeft) (hright : right.frame = some framedRight)
    (hne : left ≠ right) :
    Hashing.messageInput randomizerLeft pk framedLeft ≠
      Hashing.messageInput randomizerRight pk' framedRight := by
  intro hequal
  obtain ⟨_, _, hframed⟩ := Hashing.messageInput_injective hequal
  subst hframed
  exact hne (Message.frame_injective hleft hright)

/-- The map from a framed request to its digest input is injective, for a fixed public key
and randomizer assignment that depends only on the request. This is the form the
iid-uniformity transfer consumes: an injective family of oracle inputs. -/
theorem messageInput_injective_of_frame (pk : PublicKey)
    (frameOf : Message → Bytes) (randomizerOf : Message → Digest)
    (hframe : ∀ request : Message, request.frame = some (frameOf request)) :
    Function.Injective (fun request : Message =>
      Hashing.messageInput (randomizerOf request) pk (frameOf request)) := by
  intro left right hequal
  by_contra hne
  exact messageInput_ne_of_request_ne pk pk left right (frameOf left) (frameOf right)
    (randomizerOf left) (randomizerOf right) (hframe left) (hframe right) hne hequal

/-! ## Feeding the fresh-sampling machinery

`GraphFreshSampling` is generic over the coordinate and state types, and its hypothesis is
exactly byte-input separation: distinct coordinates must have distinct byte inputs *for every
pair of payload states*. Taking the coordinates to be the signing requests, that is precisely
`messageInput_ne_of_request_ne`.

The quantification over states is what makes this usable. In the experiment the randomizer of
a request is itself an oracle answer, so the digest input depends on the traversal state; but
separation holds whatever the randomizers are, because the framed messages already differ. So
the randomizers never have to be pinned down, and in particular no freshness or key-guessing
argument about `PRF_msg` is needed.

With `separated_messageInput`, `GraphFreshSampling.evaluate_eq_sample` applies to any
duplicate-free list of signing requests: the actual shared-oracle run equals the experiment
that draws an independent uniform thirty-byte answer per request. Parsing those answers then
gives independent uniform FORS instances, which is the hypothesis
`ForsConcentrationSharper` consumes.
-/

/-- The digest inputs of distinct signing requests are separated, for every assignment of
randomizers to requests and states — including randomizers determined by the oracle. -/
theorem separated_messageInput {State : Type} (pk : PublicKey)
    (frameOf : Message → Bytes) (randomizerOf : Message → State → Digest)
    (hframe : ∀ request : Message, request.frame = some (frameOf request)) :
    GraphFreshSampling.Separated (Index := Message) (State := State)
      (fun request state =>
        Hashing.messageInput (randomizerOf request state) pk (frameOf request)) := by
  intro left right hne leftState rightState
  exact messageInput_ne_of_request_ne pk pk left right (frameOf left) (frameOf right)
    (randomizerOf left leftState) (randomizerOf right rightState)
    (hframe left) (hframe right) hne

end SlhDsaSecurity.DigestInputDistinct
