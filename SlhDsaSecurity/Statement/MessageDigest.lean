import SlhDsaSecurity.Statement.Types

/-!
# SLH-DSA-128s message-digest layout

Algorithms 19 and 20 of FIPS 205 split the 30-byte H_msg output into 21 bytes of
FORS indices, seven bytes for the tree, and two bytes for the leaf. The latter
fields retain their low 54 and nine bits. The two plus seven unused bits remain
part of the oracle answer; parsing merely ignores them.
-/

namespace SlhDsaSecurity.MessageDigest

abbrev Instance := Fin (2 ^ totalHeight)
abbrev ForsTree := Fin forsTrees
abbrev ForsLeaf := Fin (2 ^ forsHeight)
abbrev View := Instance × (ForsTree → ForsLeaf)

def treeIndex (output : HashOutput) : BitVec (totalHeight - subtreeHeight) :=
  output.extractLsb' 16 (totalHeight - subtreeHeight)

def leafIndex (output : HashOutput) : BitVec subtreeHeight :=
  output.extractLsb' 0 subtreeHeight

/-- Fourteen 12-bit digits in big-endian order, as in base_2b. -/
def forsIndices (output : HashOutput) (tree : ForsTree) : ForsLeaf :=
  (output.extractLsb' (72 + forsHeight * (forsTrees - 1 - tree.val)) forsHeight).toFin

/-- Combine the bottom tree and leaf into the 63-bit FORS-instance index. -/
def parse (output : HashOutput) : View :=
  ((treeIndex output ++ leafIndex output).toFin, forsIndices output)

end SlhDsaSecurity.MessageDigest
