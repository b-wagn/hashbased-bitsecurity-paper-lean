/-!
# SLH-DSA-128s parameters

FIPS 205, Table 2 and Section 5. These are the standard parameters, independent of the
existing XMSS instances. In particular, each secret seed has 16 bytes.
-/

namespace SlhDsaSecurity

def n : Nat := 16
def totalHeight : Nat := 63
def layers : Nat := 7
def subtreeHeight : Nat := 9
def forsHeight : Nat := 12
def forsTrees : Nat := 14
def winternitzBits : Nat := 4
def w : Nat := 2 ^ winternitzBits
def messageDigits : Nat := 8 * n / winternitzBits
def checksumDigits : Nat := 3
def chains : Nat := messageDigits + checksumDigits

/-- Output length of H_msg, in bytes; the other hash functions output `n` bytes. -/
def messageDigestBytes : Nat := 30

/-- The cap counts all signing requests, including repetitions and failures. -/
def signingLimit : Nat := 2 ^ 64

def signatureBytes : Nat := (1 + forsTrees * (1 + forsHeight) + totalHeight + layers * chains) * n

end SlhDsaSecurity
