import «SLH-DSA-128s».Proof.Target
import «SLH-DSA-128s».Proof.SigningFaithful
import «SLH-DSA-128s».Proof.AnswerSide
import «SLH-DSA-128s».Proof.LateProvenance
import «SLH-DSA-128s».Proof.RedrawCell
import «SLH-DSA-128s».Proof.SignerRandomiser
import «SLH-DSA-128s».Proof.SharedJoin
import «SLH-DSA-128s».Proof.KeygenValue
import «SLH-DSA-128s».Proof.ServedBridge
import «SLH-DSA-128s».Proof.ServingCarrier
import «SLH-DSA-128s».Proof.ChargedProbe

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
