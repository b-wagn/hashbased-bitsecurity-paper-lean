import SlhDsaSecurity.Statement.Types

/-!
# FIPS 205 addresses

The 32-byte SHAKE address contains a 4-byte layer, a 12-byte tree, a 4-byte type,
and three 4-byte words. Changing the type clears those last three words.
-/

namespace SlhDsaSecurity

inductive AddressType where
  | wotsHash | wotsPk | tree | forsTree | forsRoots | wotsPrf | forsPrf
deriving DecidableEq

def AddressType.code : AddressType → BitVec 32
  | .wotsHash => 0
  | .wotsPk => 1
  | .tree => 2
  | .forsTree => 3
  | .forsRoots => 4
  | .wotsPrf => 5
  | .forsPrf => 6

structure Address where
  layer : BitVec 32 := 0
  tree : BitVec 96 := 0
  kind : AddressType := .wotsHash
  keyPair : BitVec 32 := 0
  chainOrHeight : BitVec 32 := 0
  hashOrIndex : BitVec 32 := 0
deriving DecidableEq

namespace Address

def toBytes (address : Address) : Bytes :=
  bytesBE 4 address.layer ++ bytesBE 12 address.tree ++ bytesBE 4 address.kind.code ++
    bytesBE 4 address.keyPair ++ bytesBE 4 address.chainOrHeight ++ bytesBE 4 address.hashOrIndex

def setTypeAndClear (address : Address) (kind : AddressType) : Address :=
  { address with kind, keyPair := 0, chainOrHeight := 0, hashOrIndex := 0 }

end Address
end SlhDsaSecurity
