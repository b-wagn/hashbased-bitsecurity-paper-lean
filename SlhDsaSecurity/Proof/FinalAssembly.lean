import SlhDsaSecurity.Proof.Target
import SlhDsaSecurity.Proof.SigningFaithful
import SlhDsaSecurity.Proof.AnswerSide
import SlhDsaSecurity.Proof.LateProvenance
import SlhDsaSecurity.Proof.RedrawCell
import SlhDsaSecurity.Proof.SignerRandomiser
import SlhDsaSecurity.Proof.SharedJoin
import SlhDsaSecurity.Proof.KeygenValue
import SlhDsaSecurity.Proof.ServedBridge
import SlhDsaSecurity.Proof.ServingCarrier
import SlhDsaSecurity.Proof.ChargedProbe

/-!
# The fused presentation's forgetting map

`forgetFused` is what a fused-tail result forgets to: the game's own outcome, count and cache.
The refining tail is the recorder's, and the one equation it owes the target is that its results
forget to the game's. That equation holds as an equality of computations: the recorder answers
every query exactly as the shared oracle does and writes its recordings beside the answer, so
dropping them returns the game.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.FinalAssembly

open Security CanonicalGraph WarmedGame RoutedSplit Target AnswerSide

/-- What a fused result forgets to: the game's own outcome, count and cache. -/
def forgetFused (result : ((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState) :
    (Outcome × Nat) × QueryCache HashSpec :=
  ((result.1.1.1, result.1.2), result.2.1)

end SlhDsaSecurity.FinalAssembly
