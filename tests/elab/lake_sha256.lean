import Lake.Build.Trace

/-!
Tests that Lake's content `Hash` is SHA-256: known-answer vectors, hex and JSON round trips,
rejection of legacy 64-bit hashes, and `Hash.mix` hashing the concatenated digests.
-/

open Lake Lean

def emptyHex := "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
def abcHex := "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"

#guard (Hash.ofString "").hex == emptyHex
#guard (Hash.ofString "abc").hex == abcHex
#guard (Hash.ofByteArray "abc".toUTF8).hex == abcHex
#guard (Hash.ofByteArray (.mk (.replicate 1000000 'a'.toNat.toUInt8))).hex ==
  "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"

-- line endings are normalized for text
#guard (Hash.ofText "a\r\nb\r\n").hex == "911169ddaaf146aff539f58c26c489af3b892dff0fe283c1c264c65ae5aa59a2"
#guard Hash.ofText "a\r\nb\r\n" == Hash.ofString "a\nb\n"

-- `mix` is SHA-256 of the two concatenated digests
#guard (Hash.mix (.ofString "") (.ofString "abc")).hex ==
  "bddbdf7e9df02f902ee5dd61b2b513d7566a2112ff97db7dc3b6d184a43ef0e3"
#guard Hash.mix (.ofString "a") (.ofString "b") != Hash.mix (.ofString "b") (.ofString "a")

-- hex round trip
#guard Hash.ofHex? abcHex == some (.ofString "abc")
#guard (Hash.ofString "abc").toString == abcHex

-- legacy 64-bit hashes and malformed strings are rejected
#guard Hash.ofHex? "0123456789abcdef" == none
#guard Hash.ofHex? (abcHex.set 0 'g') == none
#guard Hash.ofHex? (abcHex ++ "0") == none

-- JSON round trip
#guard (fromJson? (toJson (Hash.ofString "abc")) : Except String Hash).toOption ==
  some (Hash.ofString "abc")
#guard toJson (Hash.ofString "abc") == Json.str abcHex
#guard (fromJson? (Json.str "0123456789abcdef") : Except String Hash) matches .error _

-- `computeHash` on strings uses SHA-256 rather than the 64-bit `Hashable` instance
#guard pureHash "abc" == Hash.ofString "abc"
