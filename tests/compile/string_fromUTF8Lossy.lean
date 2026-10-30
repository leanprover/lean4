/-!
Compares `String.fromUTF8Lossy` with a reference implementation built on the native UTF-8 validator
`ByteArray.validateUTF8`: exhaustively on all inputs of up to two bytes and on all inputs of up to
four bytes drawn from the boundaries of the UTF-8 byte classes, and on pseudo-random inputs mixing
valid and invalid sequences. Also checks long inputs.
-/

/--
At each position, decodes the shortest valid prefix of at most four bytes. If there is none, emits
`�` and skips the current byte together with all continuation bytes (`0b10xxxxxx`) that follow it.
-/
def reference (b : ByteArray) : String := Id.run do
  let mut out := ""
  let mut i := 0
  while i < b.size do
    match [1, 2, 3, 4].find? (fun k => i + k ≤ b.size && (b.extract i (i + k)).validateUTF8) with
    | some k =>
      out := out ++ String.fromUTF8! (b.extract i (i + k))
      i := i + k
    | none =>
      out := out.push '�'
      i := i + 1
      while i < b.size && b[i]! &&& 0xc0 == 0x80 do
        i := i + 1
  return out

/-- Returns the first input on which `String.fromUTF8Lossy` and `reference` disagree. -/
def findMismatch (inputs : Array ByteArray) : Option ByteArray :=
  inputs.find? fun b => String.fromUTF8Lossy b != reference b

def report (name : String) (inputs : Array ByteArray) : IO Unit := do
  match findMismatch inputs with
  | none => IO.println s!"{name}: ok"
  | some b => IO.println s!"{name}: mismatch on {b.toList}: {(String.fromUTF8Lossy b).toList} vs {(reference b).toList}"

/-- All byte arrays of length `n` whose bytes are drawn from `bytes`. -/
def words (bytes : Array UInt8) : Nat → Array ByteArray
  | 0 => #[.empty]
  | n + 1 => (words bytes n).flatMap fun w => bytes.map w.push

/--
The first and last byte of each range that is treated uniformly by UTF-8 decoding: ASCII,
continuation bytes (split according to the second-byte restrictions after `0xE0`, `0xED`, `0xF0`
and `0xF4`), and leading bytes of overlong, regular, surrogate and out-of-range sequences.
-/
def boundaryBytes : Array UInt8 :=
  #[0x00, 0x7f, 0x80, 0x8f, 0x90, 0x9f, 0xa0, 0xbf, 0xc0, 0xc1, 0xc2, 0xdf, 0xe0, 0xe1, 0xec,
    0xed, 0xee, 0xef, 0xf0, 0xf1, 0xf3, 0xf4, 0xf5, 0xf7, 0xf8, 0xff]

def sampleChars : Array Char :=
  #['\x00', 'a', '\x7f', '\u0080', 'é', '߿', 'ࠀ', '€', '퟿', '', '￿',
    Char.ofNat 0x10000, '😀', Char.ofNat 0x10ffff]

/--
Pseudo-random concatenations of encoded sample characters, truncated encodings of sample
characters and boundary bytes.
-/
def randomInputs (count len : Nat) : Array ByteArray := Id.run do
  let mut x := 12345
  let mut out := #[]
  for _ in [0:count] do
    let mut b := ByteArray.empty
    for _ in [0:len] do
      x := (x * 1103515245 + 12345) % 2147483648
      let r := x / 65536
      let c := (String.singleton sampleChars[r % sampleChars.size]!).toByteArray
      b := match r / 256 % 3 with
        | 0 => b ++ c
        | 1 => b ++ c.extract 0 (r / 1024 % c.size)
        | _ => b.push boundaryBytes[r / 1024 % boundaryBytes.size]!
    out := out.push b
  return out

def main : IO Unit := do
  let allBytes := (Array.range 256).map UInt8.ofNat
  report "all bytes, length ≤ 2" ((List.range 3).toArray.flatMap (words allBytes))
  report "boundary bytes, length ≤ 4" ((List.range 5).toArray.flatMap (words boundaryBytes))
  report "random" (randomInputs 2000 20)
  -- Valid input is decoded unchanged.
  let s := String.join (List.replicate 10000 (String.ofList sampleChars.toList))
  IO.println (String.fromUTF8Lossy s.toByteArray == s)
  -- Long runs of invalid input are handled in a loop rather than by deep recursion.
  let conts := ByteArray.mk (Array.replicate 1000000 0x80)
  IO.println (String.fromUTF8Lossy ("a".toByteArray ++ conts ++ "b".toByteArray) == "a�b")
  IO.println (String.fromUTF8Lossy (ByteArray.mk (Array.replicate 1000000 0xff)) ==
    String.ofList (List.replicate 1000000 '�'))
