import «SLH-DSA-SHAKE-128s».Statement.Scheme
import «SLH-DSA-SHAKE-128s».Proof.HashSeparation
import VCVio.OracleComp.QueryTracking.QueryBound

/-! The final top-tree address is absent throughout the preceding key-generation work. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.KeygenUniform

def rootAddress : Address :=
  Merkle.nodeAddress (Hypertree.address (layers - 1) 0) subtreeHeight 0

def RootQuery (seed : Digest) (payload : Bytes) : OracleWorld.Domain → Prop :=
  fun input => input = .inr (Hashing.tweakableInput seed rootAddress payload)

instance (seed : Digest) (payload : Bytes) : DecidablePred (RootQuery seed payload) :=
  fun _ => inferInstanceAs (Decidable (_ = _))

noncomputable abbrev rom : QueryImpl OracleWorld (StateT (QueryCache HashSpec) ProbComp) :=
  Xmss.RandomOracleModel.impl Bytes HashOutput

end SlhDsaSecurity.KeygenUniform
