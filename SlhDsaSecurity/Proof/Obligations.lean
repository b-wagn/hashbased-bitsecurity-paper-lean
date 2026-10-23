import SlhDsaSecurity.Proof.Target
import SlhDsaSecurity.Proof.SigningFaithful

/-!
# The target at the three named events

`Target.target_of_obligations` takes its three events abstractly, because when it was proved
nobody knew what they would be. They are known now: `RoutedSplit.AnswerBad`,
`RoutedSplit.InputBad` and `ReplayGate.RandomiserBad`. This file instantiates the target at them
and so reduces the whole theorem to three statements about the warmed tail, each of which is one
piece of work rather than a design question.

The split itself is proved, and so is the one thing it asked of the game — that the signing log
holds the signer's own answers — so what the target asks for here is two bounds and nothing
else.

Keeping this file separate from `Target` is deliberate. `Target` is about arithmetic: how the
two halves and the defects fit inside `q / 2 ^ 127`, and it should stay provable without knowing
what the events are. This is where the two meet, and it is the file to read to see what is
outstanding.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.Obligations

open Security WarmedGame RoutedSplit ReplayGate Target

attribute [local irreducible] WarmedGame.afterSeeds WarmedGame.graphWalk WarmedGame.tail
  WarmedGame.warmedRun Scheme.keygenInternal Scheme.verify Scheme.sign
  Security.signingOracle Security.countQueries

/-! ## The two obligations at a refining tail

Two of the hypotheses the earlier shapes left standing are false. `hseed` is false by a byte
format: the signer's own randomiser query on a request framed as `PK.root ‖ m` *is* a message
input at the secret seed, so the event it bounds is certain on a `1 / 256` slice of key
generation. `hlate` is false because late disclosure happens, which is what it is charged for.

The repair is the same in both cases — stop assuming the event away — and differs only in what
replaces it. The seed leftover narrows to a single guess, at the forgery's own published
randomiser, which the answer side's unspent `2 ^ -126` carries. Late disclosure is **ruled out**
on the answer side and **paid** on the shared side, where the record's message-class part has
the room because the input half's bullet is claims-only.

The defect is a predicate of the recorder's recordings, which a result of `tail` does not carry,
so both obligations are stated at a refining tail — and at *an arbitrary one*, because nothing
below this file can name the presentation. The instantiation is an application, made where the
presentation is defined. -/

end SlhDsaSecurity.Obligations
