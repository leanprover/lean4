/-!
Tests `String.push` with scalar values of every UTF-8 encoding length, across many capacity
increases and on shared strings, against `String.utf8EncodeChar`.
-/

def samples : Array Char :=
  #['\x00', 'a', '\x7f', '\u0080', '\u00e9', '\u07ff', '\u0800', '\u20ac', '\ud7ff', '\ue000', '\uffff',
    Char.ofNat 0x10000, '😀', Char.ofNat 0x10ffff]

/-- A pseudo-random sequence of `n` samples. -/
def mkChars (n : Nat) : Array Char := Id.run do
  let mut out := #[]
  let mut x := 12345
  for _ in [0:n] do
    x := (x * 1103515245 + 12345) % 2147483648
    out := out.push samples[x / 65536 % samples.size]!
  return out

def check (cs : Array Char) (s : String) : Bool :=
  s.toUTF8.toList == cs.toList.flatMap String.utf8EncodeChar &&
    s.length == cs.size && s.toList == cs.toList

def main : IO Unit := do
  let cs := mkChars 20000
  -- An exclusive string, pushed to at every possible amount of spare capacity
  let mut s := ""
  for c in cs do
    s := s.push c
  IO.println (check cs s)
  -- A shared string is copied, leaving the original unchanged
  let t := s.push '😀'
  IO.println (check cs s && check (cs.push '😀') t)
  -- String literals are persistent, so they are copied as well
  IO.println ("abc".push '€' == "abc€")
