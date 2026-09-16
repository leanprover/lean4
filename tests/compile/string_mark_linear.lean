/-!
Tests that `String.markLinear` preserves the semantics of the string it marks and that the marker
survives the reallocations that `push` and `append` perform when the capacity is exhausted.
-/

def grow (n : Nat) : String := Id.run do
  let mut s := "".markLinear
  for i in 0...n do
    s := s.push (Char.ofNat ('a'.toNat + i))
  return s

def growAppend (n : Nat) : String := Id.run do
  let mut s := (grow n).markLinear
  for _ in 0...n do
    s := s ++ "xy"
  return s

def setAscii (n : Nat) : String := Id.run do
  let mut s := (grow n).markLinear
  for i in 0...n do
    s := String.Pos.Raw.set s ⟨i⟩ 'z'
  return s

def setUnicode (n : Nat) : String := Id.run do
  let mut s := (grow n).markLinear
  s := String.Pos.Raw.set s ⟨0⟩ '∀'
  return s.push 'b'

-- Printing the strings directly would append to them, which is a genuine non-linear use of the
-- marked results.
def main : IO Unit := do
  IO.println (grow 5).toList
  IO.println (growAppend 3).toList
  IO.println (setAscii 5).toList
  IO.println (setUnicode 5).toList
